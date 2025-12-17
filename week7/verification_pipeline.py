"""
Week 7: Automated Correctness Checking Pipeline

This module provides a verification pipeline that:
1. Parses Dafny programs to extract loop structure
2. Synthesizes linear invariants using Z3
3. Inserts synthesized invariants into the original Dafny program
4. Runs Dafny verification and reports results

Usage:
    python verification_pipeline.py --input program.dfy --output verified_program.dfy
    python verification_pipeline.py --input program.dfy --invariants invariants.json
"""

import re
import json
import subprocess
import argparse
import os
import sys
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Set
from enum import Enum

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'week5'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'week6'))


# ============================================================================
# Data Classes
# ============================================================================

class VerificationStatus(Enum):
    SUCCESS = "success"
    FAILURE = "failure"
    ERROR = "error"
    TIMEOUT = "timeout"


@dataclass
class LoopInfo:
    """Information about a loop in a Dafny program."""
    loop_type: str  # 'while' or 'for'
    condition: str
    variables: List[str]
    existing_invariants: List[str]
    start_line: int  # 1-indexed line number where loop starts
    header_end_line: int  # Line where loop header ends (before {)
    body_start_line: int  # Line where { appears
    body_end_line: int  # Line where } appears
    body_content: str


@dataclass
class ParsedProgram:
    """Parsed Dafny program structure."""
    method_name: str
    parameters: List[Dict[str, str]]
    returns: List[Dict[str, str]]
    preconditions: List[str]
    postconditions: List[str]
    loops: List[LoopInfo]
    original_code: str
    lines: List[str]


@dataclass
class SynthesizedInvariant:
    """A synthesized invariant."""
    expression: str
    loop_index: int  # Which loop this invariant belongs to
    strength_score: float = 0.0


@dataclass
class VerificationResult:
    """Result of Dafny verification."""
    status: VerificationStatus
    verified_count: int = 0
    error_count: int = 0
    messages: List[str] = field(default_factory=list)
    output: str = ""


# ============================================================================
# Dafny Parser (Enhanced from Week 5)
# ============================================================================

class DafnyParser:
    """
    Enhanced Dafny parser that extracts detailed program structure.
    Based on week5/parser.py with additional features for invariant insertion.
    """
    
    def __init__(self, code: str):
        self.code = code
        self.lines = code.split('\n')
    
    def parse_method_signature(self) -> Optional[Tuple[str, List[Dict], List[Dict]]]:
        """Parse method signature including name, parameters, and returns."""
        method_pattern = re.compile(
            r"method\s+(\w+)\s*\((.*?)\)\s*returns\s*\((.*?)\)", 
            re.DOTALL
        )
        match = method_pattern.search(self.code)
        if not match:
            return None
        name, params, rets = match.groups()
        return name, self._parse_params(params), self._parse_params(rets)
    
    def _parse_params(self, s: str) -> List[Dict[str, str]]:
        """Parse parameter list into structured format."""
        res = []
        for p in s.split(","):
            if ":" in p:
                n, t = p.split(":")
                res.append({"name": n.strip(), "type": t.strip()})
        return res
    
    def parse_conditions(self, keyword: str) -> List[str]:
        """Parse requires/ensures clauses."""
        pattern = re.compile(rf"{keyword}\s+([^\n]+)")
        return [c.strip().rstrip('{').strip() for c in pattern.findall(self.code)]
    
    def parse_loops(self) -> List[LoopInfo]:
        """Parse all loops with detailed position information."""
        loops = []
        loop_iterator = re.finditer(r"\b(while|for)\b", self.code)
        
        for match in loop_iterator:
            loop_type = match.group(1)
            start_pos = match.start()
            
            # Find the line number (1-indexed)
            start_line = self.code[:start_pos].count('\n') + 1
            
            # Get content after loop keyword
            post_loop = self.code[match.end():]
            brace_pos = post_loop.find("{")
            if brace_pos == -1:
                continue
                
            header = post_loop[:brace_pos]
            
            # Find header end line and body start line
            header_end_pos = match.end() + brace_pos
            header_end_line = self.code[:header_end_pos].count('\n') + 1
            body_start_line = header_end_line
            
            # Extract loop body using brace matching
            body_content = ""
            brace_count = 0
            absolute_brace_start = match.end() + brace_pos
            body_end_pos = absolute_brace_start
            
            for i, char in enumerate(self.code[absolute_brace_start:]):
                if char == "{":
                    brace_count += 1
                elif char == "}":
                    brace_count -= 1
                if brace_count == 0:
                    body_content = self.code[absolute_brace_start + 1:absolute_brace_start + i]
                    body_end_pos = absolute_brace_start + i
                    break
            
            body_end_line = self.code[:body_end_pos].count('\n') + 1
            
            # Extract existing invariants
            invariants = [inv.strip() for inv in re.findall(r"invariant\s+([^;\n{]+)", header)]
            
            # Extract condition and variables
            if loop_type == "for":
                for_match = re.search(r"(\w+)\s*:=\s*(.*?)\s+to\s+(.*?)(?=invariant|$)", header, re.DOTALL)
                if for_match:
                    var_name, start, end = for_match.groups()
                    condition = f"{start.strip()} to {end.strip()}"
                    variables = [var_name.strip()]
                else:
                    condition = "unknown"
                    variables = []
            else:
                cond_match = re.search(r"^\s*(.*?)\s*(?=invariant|$)", header, re.DOTALL)
                condition = cond_match.group(1).strip().strip("()") if cond_match else ""
                variables = self._extract_variables(condition, body_content)
            
            loops.append(LoopInfo(
                loop_type=loop_type,
                condition=condition,
                variables=variables,
                existing_invariants=invariants,
                start_line=start_line,
                header_end_line=header_end_line,
                body_start_line=body_start_line,
                body_end_line=body_end_line,
                body_content=body_content
            ))
        
        return loops
    
    def _extract_variables(self, condition: str, body: str) -> List[str]:
        """Extract loop variables from condition and body."""
        assigned = re.findall(r"\b(\w+)\s*:=", body)
        in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
        
        all_vars = set(assigned + in_cond)
        keywords = {"while", "for", "if", "else", "invariant", "var", "true", "false", "to"}
        return sorted([v for v in all_vars if v not in keywords and not v.isdigit()])
    
    def extract_initial_values(self) -> Dict[str, int]:
        """Extract initial variable values from method body."""
        init_values = {}
        # Look for var declarations with := initialization
        var_pattern = re.compile(r"var\s+(\w+)\s*:=\s*(\d+)")
        for match in var_pattern.finditer(self.code):
            var_name, value = match.groups()
            init_values[var_name] = int(value)
        return init_values
    
    def parse(self) -> Optional[ParsedProgram]:
        """Parse the complete Dafny program."""
        sig = self.parse_method_signature()
        if not sig:
            return None
        
        name, params, rets = sig
        return ParsedProgram(
            method_name=name,
            parameters=params,
            returns=rets,
            preconditions=self.parse_conditions("requires"),
            postconditions=self.parse_conditions("ensures"),
            loops=self.parse_loops(),
            original_code=self.code,
            lines=self.lines
        )


# ============================================================================
# Invariant Inserter
# ============================================================================

class InvariantInserter:
    """
    Inserts synthesized invariants into Dafny programs at the correct positions.
    """
    
    def __init__(self, parsed_program: ParsedProgram):
        self.program = parsed_program
        self.lines = list(parsed_program.lines)  # Make a copy
    
    def insert_invariants(self, invariants: List[SynthesizedInvariant]) -> str:
        """
        Insert invariants into the program at appropriate loop positions.
        
        Returns the modified program as a string.
        """
        # Group invariants by loop index
        invariants_by_loop: Dict[int, List[str]] = {}
        for inv in invariants:
            if inv.loop_index not in invariants_by_loop:
                invariants_by_loop[inv.loop_index] = []
            invariants_by_loop[inv.loop_index].append(inv.expression)
        
        # Process loops in reverse order to preserve line numbers
        sorted_loop_indices = sorted(invariants_by_loop.keys(), reverse=True)
        
        for loop_idx in sorted_loop_indices:
            if loop_idx >= len(self.program.loops):
                continue
            
            loop = self.program.loops[loop_idx]
            new_invariants = invariants_by_loop[loop_idx]
            
            self._insert_invariants_for_loop(loop, new_invariants)
        
        return '\n'.join(self.lines)
    
    def _insert_invariants_for_loop(self, loop: LoopInfo, invariants: List[str]):
        """Insert invariants for a specific loop."""
        # Find the insertion point - after the loop condition, before the {
        # We need to find the line with the loop and insert after it
        
        # Determine indentation from the loop line
        loop_line = self.lines[loop.start_line - 1]
        base_indent = len(loop_line) - len(loop_line.lstrip())
        invariant_indent = ' ' * (base_indent + 2)  # 2 spaces more than loop
        
        # Find where to insert (after existing invariants or after condition)
        insert_line = loop.start_line  # 1-indexed
        
        # Scan forward from loop start to find the { line
        for i in range(loop.start_line - 1, min(loop.body_start_line + 5, len(self.lines))):
            line = self.lines[i].strip()
            if line.startswith('{') or line.endswith('{'):
                insert_line = i + 1  # 1-indexed, insert before this line
                break
            elif 'invariant' in line.lower():
                insert_line = i + 2  # After this invariant line
        
        # Build invariant lines
        invariant_lines = [f"{invariant_indent}invariant {inv}" for inv in invariants]
        
        # Insert the lines
        for j, inv_line in enumerate(reversed(invariant_lines)):
            self.lines.insert(insert_line - 1, inv_line)
    
    def insert_invariants_from_json(self, invariants_json: Dict) -> str:
        """
        Insert invariants from a JSON structure.
        
        Expected format:
        {
            "invariants": ["0 <= i <= n + 1", "sum == i * (i - 1) / 2"]
        }
        or
        {
            "loops": [
                {"invariants": ["0 <= i <= n + 1"]}
            ]
        }
        """
        if "invariants" in invariants_json:
            # Simple format - all invariants go to first loop
            synth_invariants = [
                SynthesizedInvariant(expression=inv, loop_index=0)
                for inv in invariants_json["invariants"]
            ]
        elif "loops" in invariants_json:
            # Per-loop format
            synth_invariants = []
            for loop_idx, loop_data in enumerate(invariants_json["loops"]):
                for inv in loop_data.get("invariants", []):
                    synth_invariants.append(
                        SynthesizedInvariant(expression=inv, loop_index=loop_idx)
                    )
        else:
            synth_invariants = []
        
        return self.insert_invariants(synth_invariants)


# ============================================================================
# Dafny Verifier
# ============================================================================

class DafnyVerifier:
    """
    Executes Dafny verification and parses results.
    """
    
    def __init__(self, dafny_path: str = "dafny"):
        self.dafny_path = dafny_path
    
    def verify_file(self, filepath: str, timeout: int = 60) -> VerificationResult:
        """
        Verify a Dafny file and return the result.
        """
        try:
            result = subprocess.run(
                [self.dafny_path, "verify", filepath],
                capture_output=True,
                text=True,
                timeout=timeout
            )
            
            return self._parse_output(result.stdout, result.stderr, result.returncode)
            
        except subprocess.TimeoutExpired:
            return VerificationResult(
                status=VerificationStatus.TIMEOUT,
                messages=["Verification timed out"]
            )
        except FileNotFoundError:
            return VerificationResult(
                status=VerificationStatus.ERROR,
                messages=[f"Dafny not found at '{self.dafny_path}'. Please install Dafny and ensure it's in your PATH."]
            )
        except Exception as e:
            return VerificationResult(
                status=VerificationStatus.ERROR,
                messages=[f"Error running Dafny: {str(e)}"]
            )
    
    def verify_code(self, code: str, timeout: int = 60) -> VerificationResult:
        """
        Verify Dafny code directly by writing to a temp file.
        """
        import tempfile
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.dfy', delete=False) as f:
            f.write(code)
            temp_path = f.name
        
        try:
            result = self.verify_file(temp_path, timeout)
            return result
        finally:
            os.unlink(temp_path)
    
    def _parse_output(self, stdout: str, stderr: str, returncode: int) -> VerificationResult:
        """Parse Dafny verification output."""
        combined_output = stdout + "\n" + stderr
        messages = []
        
        # Parse verification result line
        # Example: "Dafny program verifier finished with 2 verified, 0 errors"
        result_match = re.search(
            r"Dafny program verifier finished with (\d+) verified, (\d+) errors?",
            combined_output
        )
        
        if result_match:
            verified = int(result_match.group(1))
            errors = int(result_match.group(2))
            
            if errors == 0:
                status = VerificationStatus.SUCCESS
                messages.append(f"Verification successful: {verified} assertion(s) verified")
            else:
                status = VerificationStatus.FAILURE
                messages.append(f"Verification failed: {errors} error(s)")
                
                # Extract error details
                error_lines = re.findall(r"Error:.*", combined_output)
                messages.extend(error_lines[:5])  # Limit to 5 errors
            
            return VerificationResult(
                status=status,
                verified_count=verified,
                error_count=errors,
                messages=messages,
                output=combined_output
            )
        
        # Check for other patterns
        if "Error" in combined_output or returncode != 0:
            return VerificationResult(
                status=VerificationStatus.FAILURE,
                messages=[combined_output[:500]],
                output=combined_output
            )
        
        return VerificationResult(
            status=VerificationStatus.SUCCESS,
            messages=["Verification completed"],
            output=combined_output
        )


# ============================================================================
# Linear Invariant Synthesizer (Simplified from Week 6)
# ============================================================================

class LinearInvariantSynthesizer:
    """
    Synthesizes linear invariants for loops.
    Simplified version of week6/tool-3.py for integration.
    """
    
    def __init__(self):
        self.z3_available = self._check_z3()
    
    def _check_z3(self) -> bool:
        """Check if Z3 is available."""
        try:
            from z3 import Solver
            return True
        except ImportError:
            return False
    
    def synthesize_for_loop(
        self, 
        variables: List[str], 
        init_values: Dict[str, int],
        guard: str,
        body_assignments: Dict[str, str]
    ) -> List[SynthesizedInvariant]:
        """
        Synthesize linear invariants for a loop.
        
        Returns a list of synthesized invariants.
        """
        if not self.z3_available:
            print("Warning: Z3 not available. Cannot synthesize invariants.")
            return []
        
        from z3 import Int, Solver, And, Or, Implies, ForAll, sat, IntVal, substitute, simplify
        
        invariants = []
        
        # Create Z3 variables
        z3_vars = {v: Int(v) for v in variables}
        
        # Create coefficient variables for template ax + by + ... <= c
        coeffs = {v: Int(f"a_{v}") for v in variables}
        c = Int("c")
        
        solver = Solver()
        
        # Bound coefficients to reasonable range
        for a in coeffs.values():
            solver.add(a >= -10, a <= 10)
        solver.add(c >= -50, c <= 50)
        
        # At least one coefficient must be non-zero
        solver.add(Or([coeffs[v] != 0 for v in variables]))
        
        # Initialization constraint: invariant holds at init
        init_lhs = sum(coeffs[v] * init_values.get(v, 0) for v in variables)
        solver.add(init_lhs <= c)
        
        # Try to find satisfying assignment
        if solver.check() == sat:
            model = solver.model()
            
            # Extract coefficients
            inv_coeffs = {v: model[coeffs[v]].as_long() for v in variables}
            inv_c = model[c].as_long()
            
            # Format as Dafny invariant
            inv_expr = self._format_invariant(inv_coeffs, inv_c, "<=")
            if inv_expr:
                invariants.append(SynthesizedInvariant(
                    expression=inv_expr,
                    loop_index=0,
                    strength_score=self._compute_strength(inv_coeffs, inv_c)
                ))
        
        # Also try simple bounds for each variable
        for var in variables:
            if var in init_values:
                init_val = init_values[var]
                # Variable >= initial value (common pattern for incrementing loops)
                invariants.append(SynthesizedInvariant(
                    expression=f"{var} >= {init_val}",
                    loop_index=0,
                    strength_score=50
                ))
        
        return invariants
    
    def _format_invariant(self, coeffs: Dict[str, int], c: int, op: str) -> Optional[str]:
        """Format coefficients into a readable invariant expression."""
        terms = []
        for var in sorted(coeffs.keys()):
            coef = coeffs[var]
            if coef == 0:
                continue
            
            if len(terms) == 0:
                if coef == 1:
                    terms.append(var)
                elif coef == -1:
                    terms.append(f"-{var}")
                else:
                    terms.append(f"{coef}*{var}")
            else:
                if coef > 0:
                    if coef == 1:
                        terms.append(f" + {var}")
                    else:
                        terms.append(f" + {coef}*{var}")
                else:
                    if coef == -1:
                        terms.append(f" - {var}")
                    else:
                        terms.append(f" - {abs(coef)}*{var}")
        
        if not terms:
            return None
        
        lhs = "".join(terms)
        return f"{lhs} {op} {c}"
    
    def _compute_strength(self, coeffs: Dict[str, int], c: int) -> float:
        """Compute invariant strength score."""
        score = 0.0
        total_coeff = sum(abs(v) for v in coeffs.values())
        score -= total_coeff  # Prefer smaller coefficients
        score -= abs(c) / 10  # Prefer smaller constants
        non_zero = sum(1 for v in coeffs.values() if v != 0)
        if non_zero > 1:
            score += 20  # Prefer multi-variable invariants
        return score


# ============================================================================
# Verification Pipeline
# ============================================================================

class VerificationPipeline:
    """
    Main pipeline that orchestrates the entire verification process.
    """
    
    def __init__(self, dafny_path: str = "dafny"):
        self.parser = None
        self.synthesizer = LinearInvariantSynthesizer()
        self.verifier = DafnyVerifier(dafny_path)
    
    def process_file(
        self,
        input_path: str,
        output_path: Optional[str] = None,
        invariants_json_path: Optional[str] = None,
        synthesize: bool = True,
        verify: bool = True
    ) -> Dict:
        """
        Process a Dafny file through the verification pipeline.
        
        Args:
            input_path: Path to input Dafny file
            output_path: Path to write modified program (optional)
            invariants_json_path: Path to JSON file with invariants (optional)
            synthesize: Whether to synthesize invariants automatically
            verify: Whether to verify the output program
        
        Returns:
            Dictionary with pipeline results
        """
        result = {
            "input_file": input_path,
            "status": "unknown",
            "synthesized_invariants": [],
            "verification": None,
            "output_file": None,
            "messages": []
        }
        
        # Read input file
        try:
            with open(input_path, 'r') as f:
                code = f.read()
        except Exception as e:
            result["status"] = "error"
            result["messages"].append(f"Failed to read input file: {e}")
            return result
        
        # Parse the program
        parser = DafnyParser(code)
        parsed = parser.parse()
        
        if not parsed:
            result["status"] = "error"
            result["messages"].append("Failed to parse Dafny program")
            return result
        
        result["messages"].append(f"Parsed method: {parsed.method_name}")
        result["messages"].append(f"Found {len(parsed.loops)} loop(s)")
        
        # Collect invariants
        all_invariants = []
        
        # Load invariants from JSON if provided
        if invariants_json_path:
            try:
                with open(invariants_json_path, 'r') as f:
                    json_data = json.load(f)
                for inv in json_data.get("invariants", []):
                    all_invariants.append(SynthesizedInvariant(
                        expression=inv,
                        loop_index=0
                    ))
                result["messages"].append(f"Loaded {len(all_invariants)} invariant(s) from JSON")
            except Exception as e:
                result["messages"].append(f"Warning: Failed to load invariants JSON: {e}")
        
        # Synthesize invariants if requested
        if synthesize and len(parsed.loops) > 0:
            init_values = parser.extract_initial_values()
            
            for loop_idx, loop in enumerate(parsed.loops):
                synth_invariants = self.synthesizer.synthesize_for_loop(
                    variables=loop.variables,
                    init_values=init_values,
                    guard=loop.condition,
                    body_assignments={}  # Simplified
                )
                
                for inv in synth_invariants:
                    inv.loop_index = loop_idx
                    all_invariants.append(inv)
            
            result["synthesized_invariants"] = [inv.expression for inv in all_invariants]
            result["messages"].append(f"Synthesized {len(all_invariants)} invariant(s)")
        
        # Insert invariants
        if all_invariants:
            inserter = InvariantInserter(parsed)
            modified_code = inserter.insert_invariants(all_invariants)
        else:
            modified_code = code
            result["messages"].append("No invariants to insert")
        
        # Write output file
        if output_path:
            try:
                with open(output_path, 'w') as f:
                    f.write(modified_code)
                result["output_file"] = output_path
                result["messages"].append(f"Wrote output to: {output_path}")
            except Exception as e:
                result["messages"].append(f"Warning: Failed to write output: {e}")
        
        # Verify the program
        if verify:
            if output_path:
                verification = self.verifier.verify_file(output_path)
            else:
                verification = self.verifier.verify_code(modified_code)
            
            result["verification"] = {
                "status": verification.status.value,
                "verified_count": verification.verified_count,
                "error_count": verification.error_count,
                "messages": verification.messages
            }
            
            if verification.status == VerificationStatus.SUCCESS:
                result["status"] = "success"
                result["messages"].append("✓ Verification successful!")
            else:
                result["status"] = "verification_failed"
                result["messages"].append("✗ Verification failed")
                result["messages"].extend(verification.messages)
        else:
            result["status"] = "completed"
        
        return result
    
    def process_batch(self, input_files: List[str], output_dir: str) -> List[Dict]:
        """
        Process multiple Dafny files.
        """
        results = []
        os.makedirs(output_dir, exist_ok=True)
        
        for input_path in input_files:
            basename = os.path.basename(input_path)
            output_path = os.path.join(output_dir, f"verified_{basename}")
            
            result = self.process_file(
                input_path=input_path,
                output_path=output_path
            )
            results.append(result)
        
        return results


# ============================================================================
# Command Line Interface
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Week 7: Automated Dafny Verification Pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Process a single file with automatic invariant synthesis
  python verification_pipeline.py --input program.dfy --output verified.dfy
  
  # Use pre-defined invariants from JSON
  python verification_pipeline.py --input program.dfy --invariants inv.json
  
  # Just insert invariants without verification
  python verification_pipeline.py --input program.dfy --output out.dfy --no-verify
        """
    )
    
    parser.add_argument(
        "--input", "-i",
        required=True,
        help="Input Dafny file"
    )
    
    parser.add_argument(
        "--output", "-o",
        help="Output file path (optional)"
    )
    
    parser.add_argument(
        "--invariants", "-inv",
        help="JSON file containing invariants to insert"
    )
    
    parser.add_argument(
        "--no-synthesize",
        action="store_true",
        help="Disable automatic invariant synthesis"
    )
    
    parser.add_argument(
        "--no-verify",
        action="store_true",
        help="Skip Dafny verification step"
    )
    
    parser.add_argument(
        "--dafny-path",
        default="dafny",
        help="Path to Dafny executable (default: dafny)"
    )
    
    parser.add_argument(
        "--json-output",
        action="store_true",
        help="Output results as JSON"
    )
    
    args = parser.parse_args()
    
    # Create pipeline
    pipeline = VerificationPipeline(dafny_path=args.dafny_path)
    
    # Process file
    result = pipeline.process_file(
        input_path=args.input,
        output_path=args.output,
        invariants_json_path=args.invariants,
        synthesize=not args.no_synthesize,
        verify=not args.no_verify
    )
    
    # Output results
    if args.json_output:
        print(json.dumps(result, indent=2))
    else:
        print("\n" + "="*60)
        print("Verification Pipeline Results")
        print("="*60)
        print(f"Input: {result['input_file']}")
        print(f"Status: {result['status']}")
        print()
        
        for msg in result["messages"]:
            print(f"  {msg}")
        
        if result["synthesized_invariants"]:
            print("\nSynthesized Invariants:")
            for inv in result["synthesized_invariants"]:
                print(f"  - {inv}")
        
        if result["verification"]:
            print("\nVerification Details:")
            print(f"  Verified: {result['verification']['verified_count']}")
            print(f"  Errors: {result['verification']['error_count']}")
        
        print("="*60)


if __name__ == "__main__":
    main()
