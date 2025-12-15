from z3 import *
from typing import List, Dict, Optional, Tuple, Set, Union
import re
from dataclasses import dataclass
from itertools import combinations

# ============================================================
# AST Representation (for parsing)
# ============================================================

@dataclass
class Assignment:
    var: str
    expr: str  # Right-hand side expression
    
@dataclass
class Condition:
    expr: str
    then_branch: List[Assignment]
    else_branch: List[Assignment] = None

@dataclass
class ParsedLoop:
    variables: Set[str]
    init_assignments: Dict[str, int]
    guard: str
    body: List  # Mix of Assignment and Condition objects

# ============================================================
# 1. CONSTRAINT EXTRACTION - Parse loop syntax
# ============================================================

class LoopParser:
    """Parse simple loop syntax and extract constraints"""
    
    @staticmethod
    def parse_loop_code(code: str) -> ParsedLoop:
        """
        Robustly parse loop code with support for multi-line and nested conditionals, including 'else' branches.
        """
        import re
        lines = [l.rstrip() for l in code.strip().split('\n') if l.strip()]

        variables = set()
        init_assignments = {}
        guard = None
        body = []
        current_section = None
        i = 0
        while i < len(lines):
            line = lines[i]
            if line.startswith('init:'):
                current_section = 'init'
                init_part = line[5:].strip()
                for assignment in init_part.split(','):
                    var, val = assignment.split('=')
                    var = var.strip()
                    val = int(val.strip())
                    variables.add(var)
                    init_assignments[var] = val
                i += 1
            elif line.startswith('guard:'):
                current_section = 'guard'
                guard = line[6:].strip()
                vars_in_guard = re.findall(r'\b([a-zA-Z_]\w*)\b', guard)
                variables.update(v for v in vars_in_guard if v not in ['and', 'or', 'not'])
                i += 1
            elif line.startswith('body:'):
                current_section = 'body'
                i += 1
            elif current_section == 'body':
                # Multi-line and nested conditional parser
                if line.startswith('if') and '{' in line:
                    # Parse the condition
                    cond_match = re.match(r'if\s*\(([^)]+)\)\s*\{', line)
                    if not cond_match:
                        raise ValueError(f"Malformed if statement: {line}")
                    condition = cond_match.group(1).strip()
                    # Parse the then branch (may be multi-line)
                    then_assignments = []
                    i += 1
                    brace_depth = 1
                    while i < len(lines):
                        l = lines[i]
                        if '{' in l:
                            brace_depth += l.count('{')
                        if '}' in l:
                            brace_depth -= l.count('}')
                        if brace_depth == 0:
                            break
                        if ':=' in l:
                            var, expr = l.split(':=')
                            then_assignments.append(Assignment(var.strip(), expr.strip()))
                            variables.add(var.strip())
                        i += 1
                    # Check for else branch
                    else_assignments = []
                    i += 1
                    if i < len(lines) and lines[i].startswith('else'):
                        l = lines[i]
                        if '{' in l:
                            i += 1
                            brace_depth = 1
                            while i < len(lines):
                                l2 = lines[i]
                                if '{' in l2:
                                    brace_depth += l2.count('{')
                                if '}' in l2:
                                    brace_depth -= l2.count('}')
                                if brace_depth == 0:
                                    break
                                if ':=' in l2:
                                    var, expr = l2.split(':=')
                                    else_assignments.append(Assignment(var.strip(), expr.strip()))
                                    variables.add(var.strip())
                                i += 1
                    body.append(Condition(condition, then_assignments, else_assignments if else_assignments else None))
                    i += 1
                elif ':=' in line:
                    var, expr = line.split(':=')
                    var = var.strip()
                    expr = expr.strip()
                    variables.add(var)
                    body.append(Assignment(var, expr))
                    i += 1
                else:
                    i += 1
            else:
                i += 1
        if guard is None:
            guard = ""
        return ParsedLoop(variables, init_assignments, guard, body)
    
    @staticmethod
    def extract_z3_expressions(parsed: ParsedLoop) -> Tuple[Dict, str, Dict]:
        """Convert parsed loop to Z3 expressions"""
        # Create Z3 variables
        z3_vars = {v: Int(v) for v in parsed.variables}
        
        # Convert guard to Z3
        guard_str = parsed.guard
        # Replace variable names with z3_vars["var"]
        for var in parsed.variables:
            guard_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', guard_str)
        # Convert infix logical operators to Z3 function-call form for any number of conditions
        # Handle 'not' (unary)
        guard_str = re.sub(r'\bnot\s*\(([^)]+)\)', r'Not(\1)', guard_str)
        # Handle 'and' (multiple conditions)
        if ' and ' in guard_str:
            parts = [p.strip() for p in re.split(r'\band\b', guard_str)]
            guard_str = f'And(' + ', '.join(parts) + ')'
        # Handle 'or' (multiple conditions)
        if ' or ' in guard_str:
            parts = [p.strip() for p in re.split(r'\bor\b', guard_str)]
            guard_str = f'Or(' + ', '.join(parts) + ')'
        if not guard_str.strip():
            guard_z3 = BoolVal(True)
        else:
            guard_z3 = eval(guard_str, {"z3_vars": z3_vars, "And": And, "Or": Or, "Not": Not, "BoolVal": BoolVal})
        
        # Convert body assignments to Z3 update expressions
        updates = {}
        for item in parsed.body:
            if isinstance(item, Assignment):
                expr_str = item.expr
                # Replace variable names with Z3 variables
                for var in parsed.variables:
                    expr_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', expr_str)
                updates[item.var] = eval(expr_str, {"z3_vars": z3_vars})
            elif isinstance(item, Condition):
                # For now, handle simple conditionals by creating disjunctive updates
                # More complex: would need path-sensitive analysis
                for assignment in item.then_branch:
                    if assignment.var not in updates:
                        # Conditional update: If(cond, then_expr, else_expr)
                        cond_str = item.expr
                        for var in parsed.variables:
                            cond_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', cond_str)
                        cond_z3 = eval(cond_str, {"z3_vars": z3_vars})
                        
                        expr_str = assignment.expr
                        for var in parsed.variables:
                            expr_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', expr_str)
                        then_expr = eval(expr_str, {"z3_vars": z3_vars})
                        
                        # Else branch: variable stays the same
                        else_expr = z3_vars[assignment.var]
                        
                        updates[assignment.var] = If(cond_z3, then_expr, else_expr)
        
        # For variables not updated, they stay the same
        for var in parsed.variables:
            if var not in updates:
                updates[var] = z3_vars[var]
        
        return z3_vars, guard_z3, updates

# ============================================================
# Loop Representation
# ============================================================

class Loop:
    def __init__(self, variables, init, guard, updates, z3_vars=None, source_code=None):
        self.variables = variables
        self.init = init
        self.guard = guard
        self.updates = updates
        self.z3_vars = z3_vars if z3_vars else {v: Int(v) for v in variables}
        self.source_code = source_code
    
    @staticmethod
    def from_code(code: str) -> 'Loop':
        """Create Loop from source code string"""
        parser = LoopParser()
        parsed = parser.parse_loop_code(code)
        z3_vars, guard_z3, updates = parser.extract_z3_expressions(parsed)
        
        return Loop(
            variables=list(parsed.variables),
            init=parsed.init_assignments,
            guard=guard_z3,
            updates=updates,
            z3_vars=z3_vars,
            source_code=code
        )

# ============================================================
# Invariant Representation
# ============================================================

class Invariant:
    def __init__(self, coeffs, c, inv_type, strength_score=0):
        self.coeffs = coeffs
        self.c = c
        self.type = inv_type  # "==" or "<="
        self.strength_score = strength_score
        self._normalize()
    
    def _normalize(self):
        """
        Normalize coefficients to canonical form:
        1. Divide by GCD of all coefficients
        2. Make first non-zero coefficient positive
        
        CRITICAL: Do NOT flip inequality directions during normalization.
        If we multiply by -1, we must flip <= to >=, but then we should
        reject >= inequalities entirely since our template is <= only.
        """
        from math import gcd
        from functools import reduce
        
        all_coeffs = list(self.coeffs.values()) + [self.c]
        non_zero = [abs(c) for c in all_coeffs if c != 0]
        
        if not non_zero:
            return
        
        # Find GCD of all coefficients
        g = reduce(gcd, non_zero)
        if g > 1:
            self.coeffs = {v: c // g for v, c in self.coeffs.items()}
            self.c = self.c // g
        
        # Make first non-zero coefficient positive
        # For equalities, this is safe
        # For inequalities, we need to be careful
        first_nonzero = next((self.coeffs[v] for v in sorted(self.coeffs.keys()) 
                             if self.coeffs[v] != 0), None)
        
        if first_nonzero and first_nonzero < 0:
            if self.type == "==":
                # Safe to negate both sides of equality
                self.coeffs = {v: -c for v, c in self.coeffs.items()}
                self.c = -self.c
            # For inequalities, do NOT normalize if it would flip the sign
            # This prevents creating invalid invariants
    
    def is_equivalent(self, other: 'Invariant') -> bool:
        """Check if two invariants are semantically equivalent after normalization"""
        return (self.coeffs == other.coeffs and 
                self.c == other.c and 
                self.type == other.type)
    
    def format(self):
        terms = []
        for var in sorted(self.coeffs.keys()):
            coef = self.coeffs[var]
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
        
        lhs = "".join(terms) if terms else "0"
        return f"{lhs} {self.type} {self.c}"
    
    def to_dafny(self) -> str:
        """Convert to Dafny invariant syntax"""
        terms = []
        for var in sorted(self.coeffs.keys()):
            coef = self.coeffs[var]
            if coef == 0:
                continue
            
            if coef == 1:
                terms.append(var)
            elif coef == -1:
                terms.append(f"(-{var})")
            else:
                terms.append(f"({coef} * {var})")
        
        if not terms:
            lhs = "0"
        else:
            lhs = " + ".join(terms)
        
        op = "==" if self.type == "==" else "<="
        return f"invariant {lhs} {op} {self.c}"
    
    def to_z3(self, z3_vars: Dict[str, Any]):
        """Convert to Z3 expression for use in boolean combinations"""
        lhs = sum(self.coeffs[v] * z3_vars[v] for v in self.coeffs.keys() if self.coeffs[v] != 0)
        if self.type == "==":
            return lhs == self.c
        else:
            return lhs <= self.c


# ============================================================
# Boolean Invariant Representation
# ============================================================

class BooleanInvariant:
    """
    Represents boolean combinations of linear invariants.
    Forms: 
    - Conjunction: I1 ∧ I2 ∧ ... ∧ In
    - Disjunction: I1 ∨ I2 ∨ ... ∨ In
    - DNF: (I1 ∧ I2) ∨ (I3 ∧ I4) ∨ ...
    - CNF: (I1 ∨ I2) ∧ (I3 ∨ I4) ∧ ...
    """
    
    def __init__(self, structure: str, clauses: List[Union[Invariant, List[Invariant]]], strength_score=0):
        """
        structure: "AND", "OR", "DNF", "CNF"
        clauses: 
            - For AND/OR: List[Invariant]
            - For DNF: List[List[Invariant]] (each inner list is a conjunction)
            - For CNF: List[List[Invariant]] (each inner list is a disjunction)
        """
        self.structure = structure
        self.clauses = clauses
        self.strength_score = strength_score
    
    def format(self) -> str:
        """Format as human-readable string"""
        if self.structure == "AND":
            return " ∧ ".join(f"({inv.format()})" for inv in self.clauses)
        elif self.structure == "OR":
            return " ∨ ".join(f"({inv.format()})" for inv in self.clauses)
        elif self.structure == "DNF":
            # (I1 ∧ I2) ∨ (I3 ∧ I4)
            disjuncts = []
            for conj in self.clauses:
                if len(conj) == 1:
                    disjuncts.append(conj[0].format())
                else:
                    disjuncts.append("(" + " ∧ ".join(inv.format() for inv in conj) + ")")
            return " ∨ ".join(disjuncts)
        elif self.structure == "CNF":
            # (I1 ∨ I2) ∧ (I3 ∨ I4)
            conjuncts = []
            for disj in self.clauses:
                if len(disj) == 1:
                    conjuncts.append(disj[0].format())
                else:
                    conjuncts.append("(" + " ∨ ".join(inv.format() for inv in disj) + ")")
            return " ∧ ".join(conjuncts)
        return "unknown"
    
    def to_dafny(self) -> str:
        """Convert to Dafny invariant syntax"""
        if self.structure == "AND":
            parts = [inv.format() for inv in self.clauses]
            return "invariant " + " && ".join(f"({p})" for p in parts)
        elif self.structure == "OR":
            parts = [inv.format() for inv in self.clauses]
            return "invariant " + " || ".join(f"({p})" for p in parts)
        elif self.structure == "DNF":
            disjuncts = []
            for conj in self.clauses:
                if len(conj) == 1:
                    disjuncts.append(conj[0].format())
                else:
                    disjuncts.append("(" + " && ".join(f"({inv.format()})" for inv in conj) + ")")
            return "invariant " + " || ".join(disjuncts)
        elif self.structure == "CNF":
            conjuncts = []
            for disj in self.clauses:
                if len(disj) == 1:
                    conjuncts.append(disj[0].format())
                else:
                    conjuncts.append("(" + " || ".join(f"({inv.format()})" for inv in disj) + ")")
            return "invariant " + " && ".join(conjuncts)
        return "invariant true"
    
    def to_z3(self, z3_vars: Dict[str, Any]):
        """Convert to Z3 expression"""
        if self.structure == "AND":
            return And([inv.to_z3(z3_vars) for inv in self.clauses])
        elif self.structure == "OR":
            return Or([inv.to_z3(z3_vars) for inv in self.clauses])
        elif self.structure == "DNF":
            disjuncts = []
            for conj in self.clauses:
                disjuncts.append(And([inv.to_z3(z3_vars) for inv in conj]))
            return Or(disjuncts)
        elif self.structure == "CNF":
            conjuncts = []
            for disj in self.clauses:
                conjuncts.append(Or([inv.to_z3(z3_vars) for inv in disj]))
            return And(conjuncts)
        return BoolVal(True)

# ============================================================
# Template Generation
# ============================================================

def linear_template(vars):
    coeffs = {v: Int(f"a_{v}") for v in vars}
    c = Int("c")
    return coeffs, c

# ============================================================
# Constraint Generation
# ============================================================

def initialization_constraint(coeffs, c, loop, is_equality):
    """Ensures invariant holds at loop entry"""
    lhs = sum(coeffs[v] * loop.init[v] for v in loop.variables)
    return lhs == c if is_equality else lhs <= c

def preservation_constraint(coeffs, c, loop, is_equality):
    """Ensures invariant is preserved: (Inv ∧ Guard) => Inv'"""
    z3_vars = loop.z3_vars
    
    # Current state invariant
    lhs_curr = sum(coeffs[v] * z3_vars[v] for v in loop.variables)
    inv = (lhs_curr == c) if is_equality else (lhs_curr <= c)
    
    # Next state invariant (after updates)
    lhs_next = sum(coeffs[v] * loop.updates[v] for v in loop.variables)
    inv_next = (lhs_next == c) if is_equality else (lhs_next <= c)
    
    return ForAll(
        list(z3_vars.values()),
        Implies(And(inv, loop.guard), inv_next)
    )

# ============================================================
# Termination Analysis - Ranking Functions
# ============================================================

class RankingFunction:
    """Represents a ranking function for termination proof"""
    def __init__(self, coeffs, bound):
        self.coeffs = coeffs
        self.bound = bound
    
    def format(self):
        terms = []
        for var in sorted(self.coeffs.keys()):
            coef = self.coeffs[var]
            if coef == 0:
                continue
            if coef == 1:
                terms.append(var)
            else:
                terms.append(f"{coef}*{var}")
        return " + ".join(terms) if terms else "0"

def synthesize_ranking_function(loop: Loop) -> Optional[RankingFunction]:
    """
    Find a ranking function that:
    1. Is non-negative in the loop (rank >= 0)
    2. Decreases on each iteration (rank' < rank)
    3. Is bounded below
    
    Enhanced: Try multiple strategies to find ranking functions
    """
    # Strategy 1: Standard linear ranking function
    result = _try_linear_ranking(loop)
    if result:
        return result
    
    # Strategy 2: Try with relaxed bounds
    result = _try_linear_ranking(loop, relax_bounds=True)
    if result:
        return result
    
    # Strategy 3: Try common patterns (loop bound - variable)
    result = _try_pattern_ranking(loop)
    if result:
        return result
    
    return None


def _try_linear_ranking(loop: Loop, relax_bounds: bool = False) -> Optional[RankingFunction]:
    """Try to find a linear ranking function"""
    s = Solver()
    coeffs = {v: Int(f"r_{v}") for v in loop.variables}
    
    # Bound coefficients
    max_coeff = 20 if relax_bounds else 10
    for a in coeffs.values():
        s.add(a >= -max_coeff, a <= max_coeff)
    
    # Non-triviality
    s.add(Or([coeffs[v] != 0 for v in loop.variables]))
    
    z3_vars = loop.z3_vars
    
    # Ranking function expression
    rank = sum(coeffs[v] * z3_vars[v] for v in loop.variables)
    rank_next = sum(coeffs[v] * loop.updates[v] for v in loop.variables)
    
    # Constraint 1: Non-negative when guard holds
    s.add(ForAll(list(z3_vars.values()), 
                 Implies(loop.guard, rank >= 0)))
    
    # Constraint 2: Strictly decreasing
    s.add(ForAll(list(z3_vars.values()),
                 Implies(loop.guard, rank_next < rank)))
    
    if s.check() == sat:
        m = s.model()
        return RankingFunction(
            coeffs={v: m[coeffs[v]].as_long() for v in loop.variables},
            bound=0
        )
    
    return None


def _try_pattern_ranking(loop: Loop) -> Optional[RankingFunction]:
    """
    Try common ranking function patterns:
    - For x < N: try N - x
    - For x > 0: try x
    - For decreasing loops: try the decreasing variable
    """
    # Extract bound from guard if possible
    guard_str = str(loop.guard)
    
    # Pattern: x < N  => ranking = N - x
    for var in loop.variables:
        # Check if variable is increasing
        update_expr = str(loop.updates.get(var, ""))
        if f"{var} + " in update_expr:  # x := x + ...
            # Look for upper bound in guard
            if f"{var} <" in guard_str or f"{var}<" in guard_str:
                # Try to extract the bound
                import re
                match = re.search(rf'{var}\s*<\s*(\d+)', guard_str)
                if match:
                    bound = int(match.group(1))
                    # Verify this works as a ranking function
                    coeffs = {v: (1 if v == var else 0) for v in loop.variables}
                    rf = RankingFunction(coeffs, bound)
                    if _verify_ranking_function(rf, loop, bound):
                        # Adjust coefficients: we want bound - x, so coeff should be -1
                        coeffs[var] = -1
                        # Add a constant term = bound (but we represent as coeffs only)
                        return RankingFunction(coeffs, bound)
        
        # Check if variable is decreasing
        if f"{var} - " in update_expr:  # x := x - ...
            # Variable itself might be the ranking function
            coeffs = {v: (1 if v == var else 0) for v in loop.variables}
            rf = RankingFunction(coeffs, 0)
            if _verify_ranking_function(rf, loop, 0):
                return rf
    
    return None


def _verify_ranking_function(rf: RankingFunction, loop: Loop, bound: int) -> bool:
    """Verify a candidate ranking function actually works"""
    try:
        # Quick concrete check
        state = {v: loop.init[v] for v in loop.variables}
        
        for _ in range(20):
            guard_holds = eval_z3_expr(loop.guard, state)
            if not guard_holds:
                break
            
            # Compute ranking value
            rank_val = sum(rf.coeffs.get(v, 0) * state[v] for v in loop.variables)
            
            # Check non-negative
            if rank_val < 0:
                return False
            
            # Update state
            new_state = eval_updates(loop.updates, state, loop.z3_vars)
            new_rank = sum(rf.coeffs.get(v, 0) * new_state[v] for v in loop.variables)
            
            # Check decreasing
            if new_rank >= rank_val:
                return False
            
            state = new_state
        
        return True
    except:
        return False

# ============================================================
# Invariant Strength Scoring
# ============================================================

def compute_strength(inv: Invariant, loop: Loop) -> int:
    """Rank invariants by "strength" - prefer semantic invariants over guard-dependent ones"""
    score = 0
    
    # Equalities are strongest
    if inv.type == "==":
        score += 1000  # Much higher base score for equalities
    
    # Penalize large coefficients heavily (prefer simple invariants)
    total_coeff_magnitude = sum(abs(c) for c in inv.coeffs.values())
    score -= total_coeff_magnitude * 10
    
    # Penalize large constants heavily
    score -= abs(inv.c) * 2
    
    # Reward multi-variable invariants (relational invariants are semantic)
    non_zero_coeffs = sum(1 for c in inv.coeffs.values() if c != 0)
    if non_zero_coeffs > 1:
        score += 200  # Strong bonus for relational invariants
    elif non_zero_coeffs == 1:
        # Single-variable inequalities are often guard-dependent
        score -= 100
    
    return score

# ============================================================
# Multiple Candidate Generation
# ============================================================

def generate_all_invariants(loop: Loop, is_equality: bool, max_candidates: int = 10) -> List[Invariant]:
    """Generate multiple candidate invariants using blocking clauses"""
    s = Solver()
    coeffs, c = linear_template(loop.variables)
    
    # Bounds
    for a in coeffs.values():
        s.add(a >= -10, a <= 10)
    s.add(c >= -50, c <= 50)
    
    # Non-triviality
    s.add(Or([coeffs[v] != 0 for v in loop.variables]))
    
    # Invariant constraints
    s.add(initialization_constraint(coeffs, c, loop, is_equality))
    s.add(preservation_constraint(coeffs, c, loop, is_equality))
    
    candidates = []
    seen_normalized = set()
    attempts = 0
    max_attempts = max_candidates * 3  # Allow more attempts to find valid ones
    
    while len(candidates) < max_candidates and attempts < max_attempts:
        attempts += 1
        
        if s.check() == sat:
            m = s.model()
            
            inv = Invariant(
                coeffs={v: m[coeffs[v]].as_long() for v in loop.variables},
                c=m[c].as_long(),
                inv_type="==" if is_equality else "<="
            )
            
            # Verify the invariant is actually valid before adding
            if verify_invariant(inv, loop):
                inv.strength_score = compute_strength(inv, loop)
                
                # Create normalized signature
                norm_sig = (tuple(sorted(inv.coeffs.items())), inv.c, inv.type)
                
                if norm_sig not in seen_normalized:
                    candidates.append(inv)
                    seen_normalized.add(norm_sig)
            
            # Block this solution regardless
            blocking_clause = Or([
                coeffs[v] != m[coeffs[v]] for v in loop.variables
            ] + [c != m[c]])
            s.add(blocking_clause)
        else:
            break
    
    return candidates

def verify_invariant(inv: Invariant, loop: Loop) -> bool:
    """
    Verify that an invariant actually holds by checking:
    1. Initialization
    2. A few concrete iterations
    """
    # Check initialization
    init_lhs = sum(inv.coeffs[v] * loop.init[v] for v in loop.variables)
    
    if inv.type == "==":
        if init_lhs != inv.c:
            return False
    else:  # <=
        if init_lhs > inv.c:
            return False
    
    # Check a few concrete iterations (sanity check)
    # This is a heuristic verification, not a proof
    state = {v: loop.init[v] for v in loop.variables}
    
    for iteration in range(min(5, 20)):  # Check first few iterations
        # Check if guard still holds
        guard_holds = eval_z3_expr(loop.guard, state)
        if not guard_holds:
            break
        
        # Check if invariant holds in current state
        lhs = sum(inv.coeffs[v] * state[v] for v in loop.variables)
        
        if inv.type == "==":
            if lhs != inv.c:
                return False
        else:  # <=
            if lhs > inv.c:
                return False
        
        # Update state
        state = eval_updates(loop.updates, state, loop.z3_vars)
    
    return True

def eval_z3_expr(expr, state):
    """Evaluate a Z3 expression with concrete values"""
    try:
        # Substitute concrete values
        substituted = expr
        for var, val in state.items():
            substituted = substitute(substituted, (Int(var), IntVal(val)))
        
        # Simplify and check if it's true
        simplified = simplify(substituted)
        return is_true(simplified)
    except:
        return True  # If we can't evaluate, assume it might be ok

def eval_updates(updates, state, z3_vars):
    """Evaluate update expressions with concrete values"""
    new_state = {}
    for var, update_expr in updates.items():
        try:
            # Substitute current state values
            substituted = update_expr
            for v, val in state.items():
                substituted = substitute(substituted, (z3_vars[v], IntVal(val)))
            
            # Simplify to get concrete value
            simplified = simplify(substituted)
            if simplified.is_int():
                new_state[var] = simplified.as_long()
            else:
                new_state[var] = state[var]  # Keep old value if can't evaluate
        except:
            new_state[var] = state[var]
    
    return new_state

# ============================================================
# Main Synthesis Pipeline
# ============================================================

def synthesize_linear_invariants(loop: Loop, max_total: int = 5) -> List[Invariant]:
    """Main synthesis: equality then inequality invariants"""
    all_invariants = []
    
    print("  [1/2] Searching for equality invariants...")
    eq_invs = generate_all_invariants(loop, is_equality=True, max_candidates=5)
    all_invariants.extend(eq_invs)
    print(f"        Found {len(eq_invs)} valid equality invariant(s)")
    
    print("  [2/2] Searching for inequality invariants...")
    ineq_invs = generate_all_invariants(loop, is_equality=False, max_candidates=5)
    all_invariants.extend(ineq_invs)
    print(f"        Found {len(ineq_invs)} valid inequality invariant(s)")
    
    if not all_invariants:
        print("        ⚠ No valid invariants found")
    
    # Rank by strength
    all_invariants.sort(key=lambda inv: inv.strength_score, reverse=True)
    
    return all_invariants[:max_total]


# ============================================================
# Boolean Invariant Synthesis (Week 9)
# ============================================================

def synthesize_conjunctive_invariants(loop: Loop, base_invariants: List[Invariant], 
                                     max_clauses: int = 3) -> List[BooleanInvariant]:
    """
    Synthesize conjunctive invariants: I1 ∧ I2 ∧ ... ∧ In
    These are useful when multiple constraints must hold simultaneously
    """
    candidates = []
    
    # Try combinations of 2 to max_clauses invariants
    for k in range(2, min(max_clauses + 1, len(base_invariants) + 1)):
        for combo in combinations(base_invariants, k):
            # Create conjunctive invariant
            bool_inv = BooleanInvariant("AND", list(combo))
            
            # Verify it's valid
            if verify_boolean_invariant(bool_inv, loop):
                bool_inv.strength_score = compute_boolean_strength(bool_inv, loop)
                candidates.append(bool_inv)
    
    return candidates


def synthesize_disjunctive_invariants(loop: Loop, base_invariants: List[Invariant],
                                      max_clauses: int = 3) -> List[BooleanInvariant]:
    """
    Synthesize disjunctive invariants: I1 ∨ I2 ∨ ... ∨ In
    These are useful for expressing alternative conditions
    """
    candidates = []
    
    # Try combinations of 2 to max_clauses invariants
    for k in range(2, min(max_clauses + 1, len(base_invariants) + 1)):
        for combo in combinations(base_invariants, k):
            # Create disjunctive invariant
            bool_inv = BooleanInvariant("OR", list(combo))
            
            # Verify it's valid
            if verify_boolean_invariant(bool_inv, loop):
                bool_inv.strength_score = compute_boolean_strength(bool_inv, loop)
                candidates.append(bool_inv)
    
    return candidates


def synthesize_dnf_invariants(loop: Loop, base_invariants: List[Invariant],
                              max_disjuncts: int = 2, max_per_disjunct: int = 2) -> List[BooleanInvariant]:
    """
    Synthesize DNF invariants: (I1 ∧ I2) ∨ (I3 ∧ I4) ∨ ...
    Form: disjunction of conjunctions
    """
    candidates = []
    
    # Generate conjunctions (clauses)
    conjunctions = []
    for k in range(1, min(max_per_disjunct + 1, len(base_invariants) + 1)):
        for combo in combinations(base_invariants, k):
            conjunctions.append(list(combo))
    
    # Generate disjunctions of conjunctions
    for k in range(2, min(max_disjuncts + 1, len(conjunctions) + 1)):
        for combo in combinations(conjunctions, k):
            # Create DNF invariant
            bool_inv = BooleanInvariant("DNF", list(combo))
            
            # Verify it's valid
            if verify_boolean_invariant(bool_inv, loop):
                bool_inv.strength_score = compute_boolean_strength(bool_inv, loop)
                candidates.append(bool_inv)
    
    return candidates


def synthesize_cnf_invariants(loop: Loop, base_invariants: List[Invariant],
                              max_conjuncts: int = 2, max_per_conjunct: int = 2) -> List[BooleanInvariant]:
    """
    Synthesize CNF invariants: (I1 ∨ I2) ∧ (I3 ∨ I4) ∧ ...
    Form: conjunction of disjunctions
    """
    candidates = []
    
    # Generate disjunctions (clauses)
    disjunctions = []
    for k in range(1, min(max_per_conjunct + 1, len(base_invariants) + 1)):
        for combo in combinations(base_invariants, k):
            disjunctions.append(list(combo))
    
    # Generate conjunctions of disjunctions
    for k in range(2, min(max_conjuncts + 1, len(disjunctions) + 1)):
        for combo in combinations(disjunctions, k):
            # Create CNF invariant
            bool_inv = BooleanInvariant("CNF", list(combo))
            
            # Verify it's valid
            if verify_boolean_invariant(bool_inv, loop):
                bool_inv.strength_score = compute_boolean_strength(bool_inv, loop)
                candidates.append(bool_inv)
    
    return candidates


def verify_boolean_invariant(bool_inv: BooleanInvariant, loop: Loop) -> bool:
    """Verify a boolean invariant using Z3 and concrete execution"""
    z3_vars = loop.z3_vars
    
    # Convert to Z3 expression
    inv_z3 = bool_inv.to_z3(z3_vars)
    
    # Check initialization
    init_check = inv_z3
    for var, val in loop.init.items():
        init_check = substitute(init_check, (z3_vars[var], IntVal(val)))
    
    s = Solver()
    s.add(Not(simplify(init_check)))
    if s.check() == sat:
        return False  # Invariant doesn't hold initially
    
    # Check preservation using Z3
    lhs_next = bool_inv.to_z3({v: loop.updates[v] for v in loop.variables})
    preservation = ForAll(
        list(z3_vars.values()),
        Implies(And(inv_z3, loop.guard), lhs_next)
    )
    
    s = Solver()
    s.add(Not(preservation))
    if s.check() == sat:
        return False  # Not preserved
    
    # Concrete verification (first few iterations)
    state = {v: loop.init[v] for v in loop.variables}
    for _ in range(5):
        guard_holds = eval_z3_expr(loop.guard, state)
        if not guard_holds:
            break
        
        # Check if boolean invariant holds
        if not eval_boolean_invariant(bool_inv, state):
            return False
        
        state = eval_updates(loop.updates, state, loop.z3_vars)
    
    return True


def eval_boolean_invariant(bool_inv: BooleanInvariant, state: Dict[str, int]) -> bool:
    """Evaluate boolean invariant with concrete state"""
    if bool_inv.structure == "AND":
        return all(eval_single_invariant(inv, state) for inv in bool_inv.clauses)
    elif bool_inv.structure == "OR":
        return any(eval_single_invariant(inv, state) for inv in bool_inv.clauses)
    elif bool_inv.structure == "DNF":
        # (I1 ∧ I2) ∨ (I3 ∧ I4)
        for conj in bool_inv.clauses:
            if all(eval_single_invariant(inv, state) for inv in conj):
                return True
        return False
    elif bool_inv.structure == "CNF":
        # (I1 ∨ I2) ∧ (I3 ∨ I4)
        for disj in bool_inv.clauses:
            if not any(eval_single_invariant(inv, state) for inv in disj):
                return False
        return True
    return False


def eval_single_invariant(inv: Invariant, state: Dict[str, int]) -> bool:
    """Evaluate single linear invariant with concrete state"""
    lhs = sum(inv.coeffs[v] * state.get(v, 0) for v in inv.coeffs.keys())
    if inv.type == "==":
        return lhs == inv.c
    else:  # <=
        return lhs <= inv.c


def compute_boolean_strength(bool_inv: BooleanInvariant, loop: Loop) -> int:
    """
    Score boolean invariants - heavily penalize redundancy
    A boolean invariant should only score high if it adds genuine information
    beyond what's in a single base invariant
    """
    score = 0
    
    # Check if this is just redundantly combining a strong equality with weak inequalities
    has_equality = False
    num_equalities = 0
    num_single_var_ineqs = 0
    
    if bool_inv.structure == "AND":
        for inv in bool_inv.clauses:
            if inv.type == "==":
                has_equality = True
                num_equalities += 1
            elif inv.type == "<=":
                # Check if single-variable inequality
                non_zero = sum(1 for c in inv.coeffs.values() if c != 0)
                if non_zero == 1:
                    num_single_var_ineqs += 1
        
        # If we have an equality plus single-var inequalities, this is likely redundant
        if has_equality and num_single_var_ineqs > 0:
            score -= 500  # Heavy penalty for mixing equality with trivial bounds
        
        # Base score for conjunctions
        score += 30 * len(bool_inv.clauses)
        
        # Penalize if too many clauses (likely redundant)
        if len(bool_inv.clauses) > 2:
            score -= 100 * (len(bool_inv.clauses) - 2)
            
    elif bool_inv.structure == "OR":
        # Disjunctions are weaker but can be useful
        score += 20 * len(bool_inv.clauses)
        
    elif bool_inv.structure == "DNF":
        # DNF complexity
        score += 40 * len(bool_inv.clauses)
        # Heavily penalize complex formulas
        total_atoms = sum(len(conj) for conj in bool_inv.clauses)
        score -= total_atoms * 20
        
    elif bool_inv.structure == "CNF":
        # CNF complexity
        score += 40 * len(bool_inv.clauses)
        total_atoms = sum(len(disj) for disj in bool_inv.clauses)
        score -= total_atoms * 20
    
    return score


def synthesize_all_boolean_invariants(loop: Loop, base_invariants: List[Invariant],
                                      max_results: int = 10) -> List[BooleanInvariant]:
    """
    Master function to synthesize all types of boolean invariants
    Enhanced: Filter out redundant combinations
    """
    print("\n  [Boolean Synthesis]")
    all_boolean = []
    
    if len(base_invariants) < 2:
        print("    ⚠ Need at least 2 base invariants for boolean combinations")
        return []
    
    # Separate equalities from inequalities
    equalities = [inv for inv in base_invariants if inv.type == "=="]
    inequalities = [inv for inv in base_invariants if inv.type == "<="]
    
    print(f"    Using {len(base_invariants)} base invariants ({len(equalities)} equalities, {len(inequalities)} inequalities)")
    
    # Strategy 1: Conjunctions of equalities (these are usually the strongest)
    if len(equalities) >= 2:
        print("    • Synthesizing conjunctive invariants (AND) - equalities only...")
        conj_eq = synthesize_conjunctive_invariants(loop, equalities, max_clauses=3)
        all_boolean.extend(conj_eq)
        print(f"      Found {len(conj_eq)} valid conjunction(s) of equalities")
    
    # Strategy 2: Don't mix equalities with single-variable inequalities
    # (these are almost always redundant)
    
    # Strategy 3: Conjunctions of multi-variable inequalities (can be useful)
    multi_var_ineqs = [inv for inv in inequalities 
                       if sum(1 for c in inv.coeffs.values() if c != 0) > 1]
    if len(multi_var_ineqs) >= 2:
        print("    • Synthesizing conjunctive invariants (AND) - multi-var inequalities...")
        conj_ineq = synthesize_conjunctive_invariants(loop, multi_var_ineqs, max_clauses=2)
        all_boolean.extend(conj_ineq)
        print(f"      Found {len(conj_ineq)} valid conjunction(s) of inequalities")
    
    # Strategy 4: Disjunctive invariants (useful for alternative conditions)
    if len(inequalities) >= 2:
        print("    • Synthesizing disjunctive invariants (OR)...")
        disj = synthesize_disjunctive_invariants(loop, inequalities, max_clauses=3)
        all_boolean.extend(disj)
        print(f"      Found {len(disj)} valid disjunction(s)")
    
    # Strategy 5: DNF and CNF (only for complex cases)
    if len(base_invariants) >= 4:
        print("    • Synthesizing DNF invariants...")
        dnf = synthesize_dnf_invariants(loop, base_invariants[:6], max_disjuncts=2, max_per_disjunct=2)
        # Filter to only non-trivial DNF
        dnf = [inv for inv in dnf if len(inv.clauses) >= 2]
        all_boolean.extend(dnf)
        print(f"      Found {len(dnf)} valid DNF invariant(s)")
    
    if not all_boolean:
        print("    ⚠ No useful boolean combinations found")
        return []
    
    # Rank and filter
    all_boolean.sort(key=lambda inv: inv.strength_score, reverse=True)
    
    # Additional filtering: remove obviously redundant ones
    filtered = []
    for inv in all_boolean:
        if inv.strength_score > -100:  # Skip heavily penalized invariants
            filtered.append(inv)
            if len(filtered) >= max_results:
                break
    
    return filtered

# ============================================================
# Helper Functions for Split Synthesis
# ============================================================

def evaluate_invariant(inv: Invariant, state: dict) -> bool:
    lhs = sum(inv.coeffs.get(v, 0) * state.get(v, 0) for v in inv.coeffs.keys())
    if inv.type == "==":
        return lhs == inv.c
    elif inv.type == "<=":
        return lhs <= inv.c
    return False

def evaluate_updates(updates: dict, state: dict, z3_vars: dict) -> dict:
    new_state = {}
    for var, update_expr in updates.items():
        try:
            substituted = update_expr
            for v, val in state.items():
                substituted = substitute(substituted, (z3_vars[v], IntVal(val)))
            simplified = simplify(substituted)
            if hasattr(simplified, 'is_int') and simplified.is_int():
                new_state[var] = simplified.as_long()
            else:
                new_state[var] = state.get(var, 0)
        except:
            new_state[var] = state.get(var, 0)
    return new_state

def evaluate_guard_concrete(guard, state: dict, z3_vars: dict) -> bool:
    try:
        substituted = guard
        for var, val in state.items():
            substituted = substitute(substituted, (z3_vars[var], IntVal(val)))
        simplified = simplify(substituted)
        return is_true(simplified)
    except:
        return False

def evaluate_branch(branch: ConjunctiveBranch, state: dict) -> bool:
    return all(evaluate_invariant(atom, state) for atom in branch.atoms)

# ============================================================
# Week 10: Enhanced Split Disjunctive Synthesis
# ============================================================

def is_redundant_split(branch1: ConjunctiveBranch, branch2: ConjunctiveBranch, loop: Loop) -> bool:
    """C4: Check if split is redundant"""
    z3_vars = loop.z3_vars
    s = Solver()
    b1_z3 = branch1.to_z3(z3_vars)
    b2_z3 = branch2.to_z3(z3_vars)
    
    if str(b1_z3) == str(b2_z3):
        return True
    
    s.push()
    s.add(b1_z3)
    s.add(Not(b2_z3))
    if s.check() == unsat:
        s.pop()
        return True
    s.pop()
    
    s.push()
    s.add(b2_z3)
    s.add(Not(b1_z3))
    if s.check() == unsat:
        s.pop()
        return True
    s.pop()
    
    return False

def are_branches_reachable(branch1: ConjunctiveBranch, branch2: ConjunctiveBranch, loop: Loop, max_steps: int = 100) -> bool:
    """C3: CRITICAL - Each branch must be satisfied by at least one reachable state"""
    branch1_reached = False
    branch2_reached = False
    state = loop.init.copy()
    
    for step in range(max_steps):
        if evaluate_branch(branch1, state):
            branch1_reached = True
        if evaluate_branch(branch2, state):
            branch2_reached = True
        if branch1_reached and branch2_reached:
            return True
        if not evaluate_guard_concrete(loop.guard, state, loop.z3_vars):
            break
        state = evaluate_updates(loop.updates, state, loop.z3_vars)
    
    if evaluate_branch(branch1, state):
        branch1_reached = True
    if evaluate_branch(branch2, state):
        branch2_reached = True
    
    return branch1_reached and branch2_reached

def is_inductive_alone(branch: ConjunctiveBranch, loop: Loop) -> bool:
    """Check if a single branch is inductive by itself"""
    s = Solver()
    z3_vars = loop.z3_vars
    branch_z3 = branch.to_z3(z3_vars)
    
    # Check initiation
    branch_init = branch_z3
    for var, val in loop.init.items():
        branch_init = substitute(branch_init, (z3_vars[var], IntVal(val)))
    s.push()
    s.add(Not(branch_init))
    if s.check() == sat:
        s.pop()
        return False
    s.pop()
    
    # Check preservation
    branch_next = branch.to_z3({v: loop.updates[v] for v in loop.variables})
    preservation = ForAll(list(z3_vars.values()), Implies(And(branch_z3, loop.guard), branch_next))
    s.push()
    s.add(Not(preservation))
    if s.check() == sat:
        s.pop()
        return False
    s.pop()
    
    return True

def are_branches_useful(branch1: ConjunctiveBranch, branch2: ConjunctiveBranch, loop: Loop) -> bool:
    """C5: Both branches should be useful - neither should be invariant alone"""
    if is_inductive_alone(branch1, loop):
        return False
    if is_inductive_alone(branch2, loop):
        return False
    return True

def verify_split_invariant(split_inv: BooleanInvariant, loop: Loop) -> bool:
    """Verify C1 (initiation) and C2 (inductiveness) for split invariant"""
    if split_inv.structure != "DNF" or len(split_inv.clauses) != 2:
        return False
    
    s = Solver()
    z3_vars = loop.z3_vars
    
    branch1_z3 = And([atom.to_z3(z3_vars) for atom in split_inv.clauses[0]])
    branch2_z3 = And([atom.to_z3(z3_vars) for atom in split_inv.clauses[1]])
    inv_z3 = Or(branch1_z3, branch2_z3)
    
    # C1: Initiation
    inv_init = inv_z3
    for var, val in loop.init.items():
        inv_init = substitute(inv_init, (z3_vars[var], IntVal(val)))
    s.push()
    s.add(Not(simplify(inv_init)))
    if s.check() == sat:
        s.pop()
        return False
    s.pop()
    
    # C2: Preservation
    branch1_next = And([atom.to_z3({v: loop.updates[v] for v in loop.variables}) for atom in split_inv.clauses[0]])
    branch2_next = And([atom.to_z3({v: loop.updates[v] for v in loop.variables}) for atom in split_inv.clauses[1]])
    inv_next = Or(branch1_next, branch2_next)
    preservation = ForAll(list(z3_vars.values()), Implies(And(inv_z3, loop.guard), inv_next))
    
    s.push()
    s.add(Not(preservation))
    if s.check() == sat:
        s.pop()
        return False
    s.pop()
    
    return True

def compute_split_strength(split_inv: BooleanInvariant, loop: Loop) -> int:
    """Score split invariants"""
    score = 800
    for branch_atoms in split_inv.clauses:
        for atom in branch_atoms:
            non_zero = sum(1 for c in atom.coeffs.values() if c != 0)
            if non_zero > 1:
                score += 150
    total_atoms = sum(len(branch) for branch in split_inv.clauses)
    score -= total_atoms * 30
    for branch_atoms in split_inv.clauses:
        for atom in branch_atoms:
            score -= sum(abs(c) for c in atom.coeffs.values()) * 5
    return score

def synthesize_split_disjunctive_invariants(loop: Loop, max_atoms_per_branch: int = 2) -> List[BooleanInvariant]:
    """
    Week 10: Synthesize invariants of form (Branch1 ∨ Branch2) 
    where each branch is a CONJUNCTION of linear constraints.
    
    Enforces C1-C5 constraints.
    """
    print(f"    • Synthesizing split disjunctive templates (2 branches, up to {max_atoms_per_branch} atoms each)...")
    
    # Generate base invariants
    base_invariants = synthesize_linear_invariants(loop, max_total=8)
    if len(base_invariants) < 2:
        print("      ⚠ Insufficient base invariants")
        return []
    
    # Generate candidate branches
    branches = []
    for inv in base_invariants:
        branches.append(ConjunctiveBranch([inv]))
    if max_atoms_per_branch >= 2:
        for inv1, inv2 in combinations(base_invariants, 2):
            branches.append(ConjunctiveBranch([inv1, inv2]))
    
    print(f"      Generated {len(branches)} candidate branches")
    
    # Try pairs of branches
    candidates = []
    tested = 0
    for branch1, branch2 in combinations(branches, 2):
        tested += 1
        if tested > 50:
            break
        
        split_inv = BooleanInvariant("DNF", [[atom for atom in branch1.atoms], [atom for atom in branch2.atoms]])
        
        # Apply constraints
        if is_redundant_split(branch1, branch2, loop):
            continue
        if not are_branches_reachable(branch1, branch2, loop):
            continue
        if not are_branches_useful(branch1, branch2, loop):
            continue
        if verify_split_invariant(split_inv, loop):
            split_inv.strength_score = compute_split_strength(split_inv, loop)
            candidates.append(split_inv)
            if len(candidates) >= 3:
                break
    
    candidates.sort(key=lambda x: x.strength_score, reverse=True)
    
    if candidates:
        print(f"      ✓ Found {len(candidates)} valid split invariant(s)")
    else:
        print(f"      ✗ No valid split invariants found (tested {tested} combinations)")
    
    return candidates

# ============================================================
# Dafny Code Generation
# ============================================================

def generate_dafny_code(loop: Loop, invariants: List[Invariant], ranking_fn: Optional[RankingFunction]) -> str:
    """Generate Dafny code with synthesized invariants"""
    
    code = f"method LoopExample()\n"
    
    # Variable declarations
    for var in sorted(loop.variables):
        init_val = loop.init.get(var, 0)
        code += f"  var {var}: int := {init_val};\n"
    
    code += f"  \n"
    
    # Convert guard to Dafny - handle Z3 expressions
    guard_str = str(loop.guard).replace("Not", "!").replace("And", "&&").replace("Or", "||")
    # Clean up Z3 formatting
    for var in loop.variables:
        guard_str = guard_str.replace(f"{var}", var)
    
    code += f"  while ({guard_str})\n"
    
    # Add invariants
    for inv in invariants:
        code += f"    {inv.to_dafny()}\n"
    
    # Add decreases clause for termination
    if ranking_fn:
        code += f"    decreases {ranking_fn.format()}\n"
    
    code += f"  {{\n"
    
    # Loop body - handle both simple assignments and conditionals
    if loop.source_code:
        # Parse source to generate proper Dafny statements
        parser = LoopParser()
        parsed = parser.parse_loop_code(loop.source_code)
        
        for item in parsed.body:
            if isinstance(item, Assignment):
                # Simple assignment
                code += f"    {item.var} := {item.expr};\n"
            elif isinstance(item, Condition):
                # Conditional statement
                code += f"    if ({item.expr}) {{\n"
                for assignment in item.then_branch:
                    code += f"      {assignment.var} := {assignment.expr};\n"
                code += f"    }}\n"
    else:
        # Fallback: generate from updates (won't handle conditionals correctly)
        for var in sorted(loop.variables):
            if var in loop.updates:
                update_expr = str(loop.updates[var])
                # Simplify Z3 If expressions to Dafny conditionals
                if "If(" in update_expr:
                    # This won't work well - need source code for proper conditionals
                    code += f"    // Complex update: {var}\n"
                else:
                    # Clean up expression
                    for v in loop.variables:
                        update_expr = update_expr.replace(v, v)
                    code += f"    {var} := {update_expr};\n"
    
    code += f"  }}\n"
    
    return code

# ============================================================
# Main Execution
# ============================================================
# ============================================================
# Main Execution
# ============================================================

if __name__ == "__main__":
    print("\n" + "="*70)
    print(" WEEK 10: DISJUNCTIVE INVARIANT SYNTHESIS TOOL")
    print("="*70)
    
    # Define test loops
    test_loops = [
        # # Loop 1: Standard
        # """
        # init: x=0, y=0
        # guard: x < 10
        # body:
        #   x := x + 1
        #   y := y + 1
        # """,
        # # Loop 2: Conditional Logic (Week 10 Focus)
        # # This loop increments x by different amounts based on parity
        # # Requires identifying path-sensitive properties
        """
        init:  x = 0, y = 0
        guard: x < 10
        body:
        if (x < 5) {
            x := x + 1;
            y := y + 1;
        } else {
            x := x + 1;
            y := y + 2;
        }
        """,
        # # Loop 3: The Toggle Loop (Requires Split Disjunction)
        # # x flips between 0 and 5. A linear invariant x=c is impossible.
        # # We need (x=0 OR x=5)
        """
        init:  x = 0
        guard: x < 10
        body:
        if (x < 5)
            x := x + 1
        else
            x := x + 2
        """
    ]
    
    for i, code in enumerate(test_loops, 1):
        print(f"\n{'─'*70}")
        print(f"LOOP {i} ANALYSIS")
        print('─'*70)
        print("Source:")
        print(code.strip())
        print()
        
        loop = Loop.from_code(code)
        
        # 1. Base Linear Synthesis
        print("1. Base Linear Invariant Synthesis:")
        invariants = synthesize_linear_invariants(loop, max_total=5)
        
        # 2. Combinatorial Boolean Synthesis (Week 9)
        print("\n2. Boolean Combinations (Week 9):")
        boolean_invariants = []
        if len(invariants) >= 2:
            boolean_invariants = synthesize_all_boolean_invariants(loop, invariants[:5], max_results=3)
        else:
            print("    (Insufficient base invariants for combinations)")

        # 3. Split Disjunctive Synthesis (Week 10)
        print("\n3. Split Template Synthesis (Week 10 - New):")
        # This solves for (I1 v I2) directly, finding invariants impossible via step 1 & 2
        split_invariants = synthesize_split_disjunctive_invariants(loop, max_disjuncts=2)
        
        if split_invariants:
            print(f"    ✓ Found {len(split_invariants)} split disjunctive invariant(s):")
            for j, inv in enumerate(split_invariants, 1):
                print(f"      {j}. {inv.format()}")
            boolean_invariants.extend(split_invariants)
        else:
            print("    ✗ No split disjunctive invariants found")

        # Select best invariants for Dafny
        all_invs_for_code = invariants[:2]
        if split_invariants:
            # If we found split invariants, they are likely crucial for correctness
            # We convert them to 'Invariant' objects or handle them in generation
            pass

        # Termination
        print("\n4. Termination Analysis:")
        ranking_fn = synthesize_ranking_function(loop)
        if ranking_fn:
            print(f"    ✓ Ranking function: {ranking_fn.format()}")
        
        # Generate Dafny
        print("\n5. Generated Dafny Code:")
        print("  " + "─"*66)
        
        # We construct the list of invariants to print
        # We prefer Semantic Linear > Split Disjunctive > Boolean Combos
        final_invs = invariants[:2]
        
        # Hack to print boolean invariants in the simple generator
        # (In a real tool, the generator would handle BooleanInvariant objects natively)
        print(f"method Loop{i}()")
        for var in sorted(loop.variables):
            print(f"  var {var}: int := {loop.init.get(var, 0)};")
        
        guard_str = str(loop.guard).replace("Not", "!").replace("And", "&&").replace("Or", "||")
        for var in loop.variables: guard_str = guard_str.replace(str(var), var)
        
        print(f"  while ({guard_str})")
        
        # Print Linear
        for inv in final_invs:
            print(f"    {inv.to_dafny()}")
            
        # Print Boolean/Disjunctive
        for binv in boolean_invariants[:2]:
            print(f"    {binv.to_dafny()}")
            
        if ranking_fn:
            print(f"    decreases {ranking_fn.format()}")
        print("  {")
        print("    // Body omitted for brevity (matches source)")
        print("  }")
        print("  " + "─"*66)