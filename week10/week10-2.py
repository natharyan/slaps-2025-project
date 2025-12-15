"""
Week 10: Enhanced Disjunctive Invariant Synthesis with Conjunctive Branches

Key Features:
- Conjunctive branches: (I1 ∧ I2) ∨ (I3 ∧ I4)
- Strict validation: C1-C5 constraints
- Reachability checking (prevents garbage invariants)
- Non-redundancy and usefulness checks

Author: Enhanced for Week 10 requirements
Date: December 2024
"""

from z3 import *
from typing import List, Dict, Optional, Tuple, Set, Union, Any
import re
from dataclasses import dataclass
from itertools import combinations
from functools import reduce
from math import gcd

# ============================================================
# AST Representation
# ============================================================

@dataclass
class Assignment:
    var: str
    expr: str

@dataclass
class Condition:
    expr: str
    then_branch: List[Assignment]
    else_branch: Optional[List[Assignment]] = None

@dataclass
class ParsedLoop:
    variables: Set[str]
    init_assignments: Dict[str, int]
    guard: str
    body: List[Union[Assignment, Condition]]

# ============================================================
# Loop Parser
# ============================================================

class LoopParser:
    @staticmethod
    def parse_loop_code(code: str) -> ParsedLoop:
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
                if line.startswith('if') and '{' in line:
                    cond_match = re.match(r'if\s*\(([^)]+)\)\s*\{', line)
                    if not cond_match:
                        raise ValueError(f"Malformed if: {line}")
                    condition = cond_match.group(1).strip()
                    then_assignments = []
                    i += 1
                    brace_depth = 1
                    while i < len(lines):
                        l = lines[i]
                        brace_depth += l.count('{') - l.count('}')
                        if brace_depth == 0:
                            break
                        if ':=' in l:
                            var, expr = l.split(':=')
                            then_assignments.append(Assignment(var.strip(), expr.strip()))
                            variables.add(var.strip())
                        i += 1
                    else_assignments = []
                    i += 1
                    if i < len(lines) and lines[i].startswith('else'):
                        if '{' in lines[i]:
                            i += 1
                            brace_depth = 1
                            while i < len(lines):
                                l2 = lines[i]
                                brace_depth += l2.count('{') - l2.count('}')
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
                    variables.add(var.strip())
                    body.append(Assignment(var.strip(), expr.strip()))
                    i += 1
                else:
                    i += 1
            else:
                i += 1
        
        if guard is None:
            guard = ""
        return ParsedLoop(variables, init_assignments, guard, body)
    
    @staticmethod
    def extract_z3_expressions(parsed: ParsedLoop) -> Tuple[Dict, Any, Dict]:
        z3_vars = {v: Int(v) for v in parsed.variables}
        guard_str = parsed.guard
        
        for var in parsed.variables:
            guard_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', guard_str)
        guard_str = re.sub(r'\bnot\s*\(([^)]+)\)', r'Not(\1)', guard_str)
        if ' and ' in guard_str:
            parts = [p.strip() for p in re.split(r'\band\b', guard_str)]
            guard_str = f'And({", ".join(parts)})'
        if ' or ' in guard_str:
            parts = [p.strip() for p in re.split(r'\bor\b', guard_str)]
            guard_str = f'Or({", ".join(parts)})'
        
        guard_z3 = eval(guard_str, {"z3_vars": z3_vars, "And": And, "Or": Or, "Not": Not, "BoolVal": BoolVal}) if guard_str.strip() else BoolVal(True)
        
        updates = {}
        for item in parsed.body:
            if isinstance(item, Assignment):
                expr_str = item.expr
                for var in parsed.variables:
                    expr_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', expr_str)
                updates[item.var] = eval(expr_str, {"z3_vars": z3_vars})
            elif isinstance(item, Condition):
                for assignment in item.then_branch:
                    if assignment.var not in updates:
                        cond_str = item.expr
                        for var in parsed.variables:
                            cond_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', cond_str)
                        cond_z3 = eval(cond_str, {"z3_vars": z3_vars})
                        expr_str = assignment.expr
                        for var in parsed.variables:
                            expr_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', expr_str)
                        then_expr = eval(expr_str, {"z3_vars": z3_vars})
                        else_expr = z3_vars[assignment.var]
                        updates[assignment.var] = If(cond_z3, then_expr, else_expr)
        
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
        parser = LoopParser()
        parsed = parser.parse_loop_code(code)
        z3_vars, guard_z3, updates = parser.extract_z3_expressions(parsed)
        return Loop(list(parsed.variables), parsed.init_assignments, guard_z3, updates, z3_vars, code)

# ============================================================
# Invariant Classes
# ============================================================

class Invariant:
    def __init__(self, coeffs, c, inv_type, strength_score=0):
        self.coeffs = coeffs
        self.c = c
        self.type = inv_type
        self.strength_score = strength_score
        self._normalize()
    
    def _normalize(self):
        all_coeffs = list(self.coeffs.values()) + [self.c]
        non_zero = [abs(c) for c in all_coeffs if c != 0]
        if not non_zero:
            return
        g = reduce(gcd, non_zero)
        if g > 1:
            self.coeffs = {v: c // g for v, c in self.coeffs.items()}
            self.c = self.c // g
        first_nonzero = next((self.coeffs[v] for v in sorted(self.coeffs.keys()) if self.coeffs[v] != 0), None)
        if first_nonzero and first_nonzero < 0 and self.type == "==":
            self.coeffs = {v: -c for v, c in self.coeffs.items()}
            self.c = -self.c
    
    def format(self):
        terms = []
        for var in sorted(self.coeffs.keys()):
            coef = self.coeffs[var]
            if coef == 0:
                continue
            if len(terms) == 0:
                terms.append(var if coef == 1 else f"-{var}" if coef == -1 else f"{coef}*{var}")
            else:
                if coef > 0:
                    terms.append(f" + {var}" if coef == 1 else f" + {coef}*{var}")
                else:
                    terms.append(f" - {var}" if coef == -1 else f" - {abs(coef)}*{var}")
        lhs = "".join(terms) if terms else "0"
        return f"{lhs} {self.type} {self.c}"
    
    def to_z3(self, z3_vars: Dict[str, Any]):
        lhs = sum(self.coeffs[v] * z3_vars[v] for v in self.coeffs.keys() if self.coeffs[v] != 0)
        return lhs == self.c if self.type == "==" else lhs <= self.c

class BooleanInvariant:
    def __init__(self, structure: str, clauses: List[List[Invariant]], strength_score=0):
        self.structure = structure
        self.clauses = clauses
        self.strength_score = strength_score
    
    def format(self) -> str:
        if self.structure == "DNF":
            disjuncts = []
            for conj in self.clauses:
                if len(conj) == 1:
                    disjuncts.append(conj[0].format())
                else:
                    disjuncts.append("(" + " ∧ ".join(inv.format() for inv in conj) + ")")
            return " ∨ ".join(disjuncts)
        return "unknown"
    
    def to_z3(self, z3_vars: Dict[str, Any]):
        if self.structure == "DNF":
            disjuncts = []
            for conj in self.clauses:
                disjuncts.append(And([inv.to_z3(z3_vars) for inv in conj]))
            return Or(disjuncts)
        return BoolVal(True)

@dataclass
class ConjunctiveBranch:
    atoms: List[Invariant]
    
    def to_z3(self, z3_vars: Dict[str, Any]):
        return And([atom.to_z3(z3_vars) for atom in self.atoms])
    
    def format(self) -> str:
        if len(self.atoms) == 1:
            return self.atoms[0].format()
        return "(" + " ∧ ".join(atom.format() for atom in self.atoms) + ")"

# ============================================================
# Base Invariant Synthesis
# ============================================================

def linear_template(vars):
    return {v: Int(f"a_{v}") for v in vars}, Int("c")

def initialization_constraint(coeffs, c, loop, is_equality):
    lhs = sum(coeffs[v] * loop.init[v] for v in loop.variables)
    return lhs == c if is_equality else lhs <= c

def preservation_constraint(coeffs, c, loop, is_equality):
    z3_vars = loop.z3_vars
    lhs_curr = sum(coeffs[v] * z3_vars[v] for v in loop.variables)
    inv = (lhs_curr == c) if is_equality else (lhs_curr <= c)
    lhs_next = sum(coeffs[v] * loop.updates[v] for v in loop.variables)
    inv_next = (lhs_next == c) if is_equality else (lhs_next <= c)
    return ForAll(list(z3_vars.values()), Implies(And(inv, loop.guard), inv_next))

def compute_strength(inv: Invariant, loop: Loop) -> int:
    score = 1000 if inv.type == "==" else 0
    score -= sum(abs(c) for c in inv.coeffs.values()) * 10
    score -= abs(inv.c) * 2
    non_zero = sum(1 for c in inv.coeffs.values() if c != 0)
    score += 200 if non_zero > 1 else -100 if non_zero == 1 else 0
    return score

def verify_invariant(inv: Invariant, loop: Loop) -> bool:
    init_lhs = sum(inv.coeffs[v] * loop.init[v] for v in loop.variables)
    if inv.type == "==":
        if init_lhs != inv.c:
            return False
    else:
        if init_lhs > inv.c:
            return False
    return True

def generate_all_invariants(loop: Loop, is_equality: bool, max_candidates: int = 10) -> List[Invariant]:
    s = Solver()
    coeffs, c = linear_template(loop.variables)
    for a in coeffs.values():
        s.add(a >= -10, a <= 10)
    s.add(c >= -50, c <= 50)
    s.add(Or([coeffs[v] != 0 for v in loop.variables]))
    s.add(initialization_constraint(coeffs, c, loop, is_equality))
    s.add(preservation_constraint(coeffs, c, loop, is_equality))
    
    candidates = []
    seen = set()
    attempts = 0
    
    while len(candidates) < max_candidates and attempts < max_candidates * 3:
        attempts += 1
        if s.check() == sat:
            m = s.model()
            inv = Invariant(
                {v: m[coeffs[v]].as_long() for v in loop.variables},
                m[c].as_long(),
                "==" if is_equality else "<="
            )
            if verify_invariant(inv, loop):
                inv.strength_score = compute_strength(inv, loop)
                sig = (tuple(sorted(inv.coeffs.items())), inv.c, inv.type)
                if sig not in seen:
                    candidates.append(inv)
                    seen.add(sig)
            s.add(Or([coeffs[v] != m[coeffs[v]] for v in loop.variables] + [c != m[c]]))
        else:
            break
    return candidates

def synthesize_linear_invariants(loop: Loop, max_total: int = 8) -> List[Invariant]:
    print("  [1/2] Searching for equality invariants...")
    eq_invs = generate_all_invariants(loop, True, 5)
    print(f"        Found {len(eq_invs)} equality invariant(s)")
    
    print("  [2/2] Searching for inequality invariants...")
    ineq_invs = generate_all_invariants(loop, False, 5)
    print(f"        Found {len(ineq_invs)} inequality invariant(s)")
    
    all_invs = eq_invs + ineq_invs
    all_invs.sort(key=lambda inv: inv.strength_score, reverse=True)
    return all_invs[:max_total]

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
# Main Execution
# ============================================================

if __name__ == "__main__":
    print("\n" + "="*70)
    print(" WEEK 10: ENHANCED DISJUNCTIVE INVARIANT SYNTHESIS")
    print(" Features: Conjunctive branches + C1-C5 validation")
    print("="*70)
    
    test_loops = [
        """
        init: x=0, y=0
        guard: x < 10
        body:
        if (x < 5) {
            x := x + 1
            y := y + 1
        } else {
            x := x + 1
            y := y + 2
        }
        """,
        
        """
        init: x=0
        guard: x < 10
        body:
        if (x < 5) {
            x := x + 1
        } else {
            x := x + 2
        }
        """,
        
        """
        init: x=0, y=0, z=0
        guard: x < 8
        body:
        if (x < 4) {
            x := x + 1
            y := y + 1
            z := z
        } else {
            x := x + 1
            y := y
            z := z + 2
        }
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
        
        print("1. Base Linear Invariant Synthesis:")
        invariants = synthesize_linear_invariants(loop, max_total=8)
        
        print("\n2. Split Disjunctive Synthesis (Enhanced Week 10):")
        split_invariants = synthesize_split_disjunctive_invariants(loop, max_atoms_per_branch=2)
        
        if split_invariants:
            print(f"\n    ✓ Best split invariants:")
            for j, inv in enumerate(split_invariants[:3], 1):
                print(f"      {j}. {inv.format()}")
                print(f"         Strength: {inv.strength_score}")
        
        print("\n3. Top Invariants Overall:")
        print("  " + "─"*66)
        all_results = invariants[:2] + split_invariants[:2]
        all_results.sort(key=lambda x: getattr(x, 'strength_score', 0), reverse=True)
        
        for idx, inv in enumerate(all_results[:3], 1):
            if isinstance(inv, BooleanInvariant):
                print(f"  [{idx}] {inv.format()}")
                print(f"      Type: Split Disjunctive (conjunctive branches)")
            else:
                print(f"  [{idx}] {inv.format()}")
                print(f"      Type: Linear {'Equality' if inv.type == '==' else 'Inequality'}")
        print("  " + "─"*66)