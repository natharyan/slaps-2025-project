from z3 import *
from typing import List, Dict, Optional, Tuple, Set, Union
import re
from dataclasses import dataclass
from itertools import combinations

@dataclass
class Assignment:
    var: str
    expr: str  
    
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
    body: List  

class LoopParser:
    
    @staticmethod
    def parse_loop_code(code: str) -> ParsedLoop:
        """
        Parse loop code is like:
        init: x=0, y=0
        guard: x < 10
        body:
          x := x + 1
          if (y > 5) { z := z + 1 }
        """
        lines = [l.strip() for l in code.strip().split('\n') if l.strip()]
        
        variables = set()
        init_assignments = {}
        guard = None
        body = []
        
        current_section = None
        
        for line in lines:
            if line.startswith('init:'):
                current_section = 'init'
                init_part = line[5:].strip()
                for assignment in init_part.split(','):
                    var, val = assignment.split('=')
                    var = var.strip()
                    val = int(val.strip())
                    variables.add(var)
                    init_assignments[var] = val
                    
            elif line.startswith('guard:'):
                current_section = 'guard'
                guard = line[6:].strip()
                vars_in_guard = re.findall(r'\b([a-zA-Z_]\w*)\b', guard)
                variables.update(v for v in vars_in_guard if v not in ['and', 'or', 'not'])
                
            elif line.startswith('body:'):
                current_section = 'body'
                
            elif current_section == 'body':
                if 'if' in line and '{' in line:
                    cond_match = re.search(r'if\s*\(([^)]+)\)\s*\{([^}]+)\}', line)
                    if cond_match:
                        condition = cond_match.group(1).strip()
                        then_stmt = cond_match.group(2).strip()
                        
                        then_assignments = []
                        if ':=' in then_stmt:
                            var, expr = then_stmt.split(':=')
                            then_assignments.append(Assignment(var.strip(), expr.strip()))
                            variables.add(var.strip())
                        
                        body.append(Condition(condition, then_assignments))
                        
                elif ':=' in line:
                    var, expr = line.split(':=')
                    var = var.strip()
                    expr = expr.strip()
                    variables.add(var)
                    body.append(Assignment(var, expr))
        
        return ParsedLoop(variables, init_assignments, guard, body)
    
    @staticmethod
    def extract_z3_expressions(parsed: ParsedLoop) -> Tuple[Dict, str, Dict]:
        z3_vars = {v: Int(v) for v in parsed.variables}
        
        guard_str = parsed.guard
        for var in parsed.variables:
            guard_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', guard_str)
        guard_str = re.sub(r'\bnot\s*\(([^)]+)\)', r'Not(\1)', guard_str)
        if ' and ' in guard_str:
            parts = [p.strip() for p in re.split(r'\band\b', guard_str)]
            guard_str = f'And(' + ', '.join(parts) + ')'
        if ' or ' in guard_str:
            parts = [p.strip() for p in re.split(r'\bor\b', guard_str)]
            guard_str = f'Or(' + ', '.join(parts) + ')'
        guard_z3 = eval(guard_str, {"z3_vars": z3_vars, "And": And, "Or": Or, "Not": Not})
        
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
        
        return Loop(
            variables=list(parsed.variables),
            init=parsed.init_assignments,
            guard=guard_z3,
            updates=updates,
            z3_vars=z3_vars,
            source_code=code
        )

class Invariant:
    def __init__(self, coeffs, c, inv_type, strength_score=0):
        self.coeffs = coeffs
        self.c = c
        self.type = inv_type  
        self.strength_score = strength_score
        self._normalize()
    
    def _normalize(self):
        from math import gcd
        from functools import reduce
        
        all_coeffs = list(self.coeffs.values()) + [self.c]
        non_zero = [abs(c) for c in all_coeffs if c != 0]
        
        if not non_zero:
            return
        
        g = reduce(gcd, non_zero)
        if g > 1:
            self.coeffs = {v: c // g for v, c in self.coeffs.items()}
            self.c = self.c // g

        first_nonzero = next((self.coeffs[v] for v in sorted(self.coeffs.keys()) 
                             if self.coeffs[v] != 0), None)
        
        if first_nonzero and first_nonzero < 0:
            if self.type == "==":
                self.coeffs = {v: -c for v, c in self.coeffs.items()}
                self.c = -self.c
    
    def is_equivalent(self, other: 'Invariant') -> bool:
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
        lhs = sum(self.coeffs[v] * z3_vars[v] for v in self.coeffs.keys() if self.coeffs[v] != 0)
        if self.type == "==":
            return lhs == self.c
        else:
            return lhs <= self.c

class BooleanInvariant:
    
    def __init__(self, structure: str, clauses: List[Union[Invariant, List[Invariant]]], strength_score=0):
        self.structure = structure
        self.clauses = clauses
        self.strength_score = strength_score
    
    def format(self) -> str:
        if self.structure == "AND":
            return " ∧ ".join(f"({inv.format()})" for inv in self.clauses)
        elif self.structure == "OR":
            return " ∨ ".join(f"({inv.format()})" for inv in self.clauses)
        elif self.structure == "DNF":
            disjuncts = []
            for conj in self.clauses:
                if len(conj) == 1:
                    disjuncts.append(conj[0].format())
                else:
                    disjuncts.append("(" + " ∧ ".join(inv.format() for inv in conj) + ")")
            return " ∨ ".join(disjuncts)
        elif self.structure == "CNF":
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

def linear_template(vars):
    coeffs = {v: Int(f"a_{v}") for v in vars}
    c = Int("c")
    return coeffs, c

def initialization_constraint(coeffs, c, loop, is_equality):
    lhs = sum(coeffs[v] * loop.init[v] for v in loop.variables)
    return lhs == c if is_equality else lhs <= c

def preservation_constraint(coeffs, c, loop, is_equality):
    z3_vars = loop.z3_vars
    lhs_curr = sum(coeffs[v] * z3_vars[v] for v in loop.variables)
    inv = (lhs_curr == c) if is_equality else (lhs_curr <= c)
    lhs_next = sum(coeffs[v] * loop.updates[v] for v in loop.variables)
    inv_next = (lhs_next == c) if is_equality else (lhs_next <= c)
    
    return ForAll(
        list(z3_vars.values()),
        Implies(And(inv, loop.guard), inv_next)
    )

class RankingFunction:
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
    s = Solver()
    coeffs = {v: Int(f"r_{v}") for v in loop.variables}
    
    max_coeff = 20 if relax_bounds else 10
    for a in coeffs.values():
        s.add(a >= -max_coeff, a <= max_coeff)

    s.add(Or([coeffs[v] != 0 for v in loop.variables]))
    
    z3_vars = loop.z3_vars
    
    rank = sum(coeffs[v] * z3_vars[v] for v in loop.variables)
    rank_next = sum(coeffs[v] * loop.updates[v] for v in loop.variables)
    
    s.add(ForAll(list(z3_vars.values()), 
                 Implies(loop.guard, rank >= 0)))
    
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
    guard_str = str(loop.guard)
    
    for var in loop.variables:
        update_expr = str(loop.updates.get(var, ""))
        if f"{var} + " in update_expr:  
            if f"{var} <" in guard_str or f"{var}<" in guard_str:
                import re
                match = re.search(rf'{var}\s*<\s*(\d+)', guard_str)
                if match:
                    bound = int(match.group(1))
                    coeffs = {v: (1 if v == var else 0) for v in loop.variables}
                    rf = RankingFunction(coeffs, bound)
                    if _verify_ranking_function(rf, loop, bound):
                        coeffs[var] = -1
                        return RankingFunction(coeffs, bound)
        
        if f"{var} - " in update_expr:  
            coeffs = {v: (1 if v == var else 0) for v in loop.variables}
            rf = RankingFunction(coeffs, 0)
            if _verify_ranking_function(rf, loop, 0):
                return rf
    
    return None


def _verify_ranking_function(rf: RankingFunction, loop: Loop, bound: int) -> bool:
    try:
        state = {v: loop.init[v] for v in loop.variables}
        
        for _ in range(20):
            guard_holds = eval_z3_expr(loop.guard, state)
            if not guard_holds:
                break
            
            rank_val = sum(rf.coeffs.get(v, 0) * state[v] for v in loop.variables)
            
            if rank_val < 0:
                return False
            
            new_state = eval_updates(loop.updates, state, loop.z3_vars)
            new_rank = sum(rf.coeffs.get(v, 0) * new_state[v] for v in loop.variables)
            
            if new_rank >= rank_val:
                return False
            
            state = new_state
        
        return True
    except:
        return False

def compute_strength(inv: Invariant, loop: Loop) -> int:
    score = 0
    
    if inv.type == "==":
        score += 1000 
    
    total_coeff_magnitude = sum(abs(c) for c in inv.coeffs.values())
    score -= total_coeff_magnitude * 10
    
    score -= abs(inv.c) * 2
    
    non_zero_coeffs = sum(1 for c in inv.coeffs.values() if c != 0)
    if non_zero_coeffs > 1:
        score += 200  
    elif non_zero_coeffs == 1:
        score -= 100
    
    return score

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
    seen_normalized = set()
    attempts = 0
    max_attempts = max_candidates * 3  
    
    while len(candidates) < max_candidates and attempts < max_attempts:
        attempts += 1
        
        if s.check() == sat:
            m = s.model()
            
            inv = Invariant(
                coeffs={v: m[coeffs[v]].as_long() for v in loop.variables},
                c=m[c].as_long(),
                inv_type="==" if is_equality else "<="
            )
            
            if verify_invariant(inv, loop):
                inv.strength_score = compute_strength(inv, loop)
                
                norm_sig = (tuple(sorted(inv.coeffs.items())), inv.c, inv.type)
                
                if norm_sig not in seen_normalized:
                    candidates.append(inv)
                    seen_normalized.add(norm_sig)
            
            blocking_clause = Or([
                coeffs[v] != m[coeffs[v]] for v in loop.variables
            ] + [c != m[c]])
            s.add(blocking_clause)
        else:
            break
    
    return candidates

def verify_invariant(inv: Invariant, loop: Loop) -> bool:
    init_lhs = sum(inv.coeffs[v] * loop.init[v] for v in loop.variables)
    
    if inv.type == "==":
        if init_lhs != inv.c:
            return False
    else:  # <=
        if init_lhs > inv.c:
            return False
    
    state = {v: loop.init[v] for v in loop.variables}
    
    for iteration in range(min(5, 20)):  
        guard_holds = eval_z3_expr(loop.guard, state)
        if not guard_holds:
            break
        
        lhs = sum(inv.coeffs[v] * state[v] for v in loop.variables)
        
        if inv.type == "==":
            if lhs != inv.c:
                return False
        else:  
            if lhs > inv.c:
                return False
        
        state = eval_updates(loop.updates, state, loop.z3_vars)
    
    return True

def eval_z3_expr(expr, state):
    try:
        substituted = expr
        for var, val in state.items():
            substituted = substitute(substituted, (Int(var), IntVal(val)))
        
        simplified = simplify(substituted)
        return is_true(simplified)
    except:
        return True  

def eval_updates(updates, state, z3_vars):
    new_state = {}
    for var, update_expr in updates.items():
        try:
            substituted = update_expr
            for v, val in state.items():
                substituted = substitute(substituted, (z3_vars[v], IntVal(val)))
            
            simplified = simplify(substituted)
            if simplified.is_int():
                new_state[var] = simplified.as_long()
            else:
                new_state[var] = state[var]  
        except:
            new_state[var] = state[var]
    
    return new_state

def synthesize_linear_invariants(loop: Loop, max_total: int = 5) -> List[Invariant]:
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
        print("No valid invariants found")
    
    all_invariants.sort(key=lambda inv: inv.strength_score, reverse=True)
    
    return all_invariants[:max_total]



def synthesize_conjunctive_invariants(loop: Loop, base_invariants: List[Invariant], 
                                     max_clauses: int = 3) -> List[BooleanInvariant]:
    candidates = []
    
    for k in range(2, min(max_clauses + 1, len(base_invariants) + 1)):
        for combo in combinations(base_invariants, k):
            bool_inv = BooleanInvariant("AND", list(combo))
            
            if verify_boolean_invariant(bool_inv, loop):
                bool_inv.strength_score = compute_boolean_strength(bool_inv, loop)
                candidates.append(bool_inv)
    
    return candidates


def synthesize_disjunctive_invariants(loop: Loop, base_invariants: List[Invariant],
                                      max_clauses: int = 3) -> List[BooleanInvariant]:
    candidates = []
    
    for k in range(2, min(max_clauses + 1, len(base_invariants) + 1)):
        for combo in combinations(base_invariants, k):
            bool_inv = BooleanInvariant("OR", list(combo))
            
            if verify_boolean_invariant(bool_inv, loop):
                bool_inv.strength_score = compute_boolean_strength(bool_inv, loop)
                candidates.append(bool_inv)
    
    return candidates


def synthesize_dnf_invariants(loop: Loop, base_invariants: List[Invariant],
                              max_disjuncts: int = 2, max_per_disjunct: int = 2) -> List[BooleanInvariant]:
    candidates = []
    
    conjunctions = []
    for k in range(1, min(max_per_disjunct + 1, len(base_invariants) + 1)):
        for combo in combinations(base_invariants, k):
            conjunctions.append(list(combo))
    
    for k in range(2, min(max_disjuncts + 1, len(conjunctions) + 1)):
        for combo in combinations(conjunctions, k):
            bool_inv = BooleanInvariant("DNF", list(combo))
            
            if verify_boolean_invariant(bool_inv, loop):
                bool_inv.strength_score = compute_boolean_strength(bool_inv, loop)
                candidates.append(bool_inv)
    
    return candidates


def synthesize_cnf_invariants(loop: Loop, base_invariants: List[Invariant],
                              max_conjuncts: int = 2, max_per_conjunct: int = 2) -> List[BooleanInvariant]:
    candidates = []
    
    disjunctions = []
    for k in range(1, min(max_per_conjunct + 1, len(base_invariants) + 1)):
        for combo in combinations(base_invariants, k):
            disjunctions.append(list(combo))
    
    for k in range(2, min(max_conjuncts + 1, len(disjunctions) + 1)):
        for combo in combinations(disjunctions, k):
            bool_inv = BooleanInvariant("CNF", list(combo))
            
            if verify_boolean_invariant(bool_inv, loop):
                bool_inv.strength_score = compute_boolean_strength(bool_inv, loop)
                candidates.append(bool_inv)
    
    return candidates


def verify_boolean_invariant(bool_inv: BooleanInvariant, loop: Loop) -> bool:
    z3_vars = loop.z3_vars
    
    inv_z3 = bool_inv.to_z3(z3_vars)
    
    init_check = inv_z3
    for var, val in loop.init.items():
        init_check = substitute(init_check, (z3_vars[var], IntVal(val)))
    
    s = Solver()
    s.add(Not(simplify(init_check)))
    if s.check() == sat:
        return False  
    
    lhs_next = bool_inv.to_z3({v: loop.updates[v] for v in loop.variables})
    preservation = ForAll(
        list(z3_vars.values()),
        Implies(And(inv_z3, loop.guard), lhs_next)
    )
    
    s = Solver()
    s.add(Not(preservation))
    if s.check() == sat:
        return False  
    
    state = {v: loop.init[v] for v in loop.variables}
    for _ in range(5):
        guard_holds = eval_z3_expr(loop.guard, state)
        if not guard_holds:
            break
        
        if not eval_boolean_invariant(bool_inv, state):
            return False
        
        state = eval_updates(loop.updates, state, loop.z3_vars)
    
    return True


def eval_boolean_invariant(bool_inv: BooleanInvariant, state: Dict[str, int]) -> bool:
    if bool_inv.structure == "AND":
        return all(eval_single_invariant(inv, state) for inv in bool_inv.clauses)
    elif bool_inv.structure == "OR":
        return any(eval_single_invariant(inv, state) for inv in bool_inv.clauses)
    elif bool_inv.structure == "DNF":
        for conj in bool_inv.clauses:
            if all(eval_single_invariant(inv, state) for inv in conj):
                return True
        return False
    elif bool_inv.structure == "CNF":
        for disj in bool_inv.clauses:
            if not any(eval_single_invariant(inv, state) for inv in disj):
                return False
        return True
    return False


def eval_single_invariant(inv: Invariant, state: Dict[str, int]) -> bool:
    lhs = sum(inv.coeffs[v] * state.get(v, 0) for v in inv.coeffs.keys())
    if inv.type == "==":
        return lhs == inv.c
    else:  # <=
        return lhs <= inv.c


def compute_boolean_strength(bool_inv: BooleanInvariant, loop: Loop) -> int:
    score = 0
    
    has_equality = False
    num_equalities = 0
    num_single_var_ineqs = 0
    
    if bool_inv.structure == "AND":
        for inv in bool_inv.clauses:
            if inv.type == "==":
                has_equality = True
                num_equalities += 1
            elif inv.type == "<=":
                non_zero = sum(1 for c in inv.coeffs.values() if c != 0)
                if non_zero == 1:
                    num_single_var_ineqs += 1
        
        if has_equality and num_single_var_ineqs > 0:
            score -= 500  
        
        score += 30 * len(bool_inv.clauses)
        
        if len(bool_inv.clauses) > 2:
            score -= 100 * (len(bool_inv.clauses) - 2)
            
    elif bool_inv.structure == "OR":
        score += 20 * len(bool_inv.clauses)
        
    elif bool_inv.structure == "DNF":
        score += 40 * len(bool_inv.clauses)
        total_atoms = sum(len(conj) for conj in bool_inv.clauses)
        score -= total_atoms * 20
        
    elif bool_inv.structure == "CNF":
        score += 40 * len(bool_inv.clauses)
        total_atoms = sum(len(disj) for disj in bool_inv.clauses)
        score -= total_atoms * 20
    
    return score


def synthesize_all_boolean_invariants(loop: Loop, base_invariants: List[Invariant],
                                      max_results: int = 10) -> List[BooleanInvariant]:
    print("\n  [Boolean Synthesis]")
    all_boolean = []
    
    if len(base_invariants) < 2:
        print("Need at least 2 base invariants for boolean combinations")
        return []
    
    equalities = [inv for inv in base_invariants if inv.type == "=="]
    inequalities = [inv for inv in base_invariants if inv.type == "<="]
    
    print(f"Using {len(base_invariants)} base invariants ({len(equalities)} equalities, {len(inequalities)} inequalities)")
    
    if len(equalities) >= 2:
        print("Synthesizing conjunctive invariants (AND) - equalities only...")
        conj_eq = synthesize_conjunctive_invariants(loop, equalities, max_clauses=3)
        all_boolean.extend(conj_eq)
        print(f"      Found {len(conj_eq)} valid conjunction(s) of equalities")
    
    multi_var_ineqs = [inv for inv in inequalities 
                       if sum(1 for c in inv.coeffs.values() if c != 0) > 1]
    if len(multi_var_ineqs) >= 2:
        print("Synthesizing conjunctive invariants (AND) - multi-var inequalities...")
        conj_ineq = synthesize_conjunctive_invariants(loop, multi_var_ineqs, max_clauses=2)
        all_boolean.extend(conj_ineq)
        print(f"      Found {len(conj_ineq)} valid conjunction(s) of inequalities")
    
    if len(inequalities) >= 2:
        print("Synthesizing disjunctive invariants (OR)...")
        disj = synthesize_disjunctive_invariants(loop, inequalities, max_clauses=3)
        all_boolean.extend(disj)
        print(f"      Found {len(disj)} valid disjunction(s)")
    

    if len(base_invariants) >= 4:
        print("Synthesizing DNF invariants...")
        dnf = synthesize_dnf_invariants(loop, base_invariants[:6], max_disjuncts=2, max_per_disjunct=2)
        # Filter to only non-trivial DNF
        dnf = [inv for inv in dnf if len(inv.clauses) >= 2]
        all_boolean.extend(dnf)
        print(f"      Found {len(dnf)} valid DNF invariant(s)")
    
    if not all_boolean:
        print("   No useful boolean combinations found")
        return []
    
    all_boolean.sort(key=lambda inv: inv.strength_score, reverse=True)
    
    filtered = []
    for inv in all_boolean:
        if inv.strength_score > -100: 
            filtered.append(inv)
            if len(filtered) >= max_results:
                break
    
    return filtered

def generate_dafny_code(loop: Loop, invariants: List[Invariant], ranking_fn: Optional[RankingFunction]) -> str:
    
    code = f"method LoopExample()\n"
    
    for var in sorted(loop.variables):
        init_val = loop.init.get(var, 0)
        code += f"  var {var}: int := {init_val};\n"
    
    code += f"  \n"
    
    guard_str = str(loop.guard).replace("Not", "!").replace("And", "&&").replace("Or", "||")
    for var in loop.variables:
        guard_str = guard_str.replace(f"{var}", var)
    
    code += f"  while ({guard_str})\n"
    
    for inv in invariants:
        code += f"    {inv.to_dafny()}\n"
    
    if ranking_fn:
        code += f"    decreases {ranking_fn.format()}\n"
    
    code += f"  {{\n"
    
    if loop.source_code:
        parser = LoopParser()
        parsed = parser.parse_loop_code(loop.source_code)
        
        for item in parsed.body:
            if isinstance(item, Assignment):
                code += f"    {item.var} := {item.expr};\n"
            elif isinstance(item, Condition):
                code += f"    if ({item.expr}) {{\n"
                for assignment in item.then_branch:
                    code += f"      {assignment.var} := {assignment.expr};\n"
                code += f"    }}\n"
    else:
        for var in sorted(loop.variables):
            if var in loop.updates:
                update_expr = str(loop.updates[var])
                if "If(" in update_expr:
                    code += f"    // Complex update: {var}\n"
                else:
                    for v in loop.variables:
                        update_expr = update_expr.replace(v, v)
                    code += f"    {var} := {update_expr};\n"
    
    code += f"  }}\n"
    
    return code

if __name__ == "__main__":
    test_loops = [
        """
        init: x=0, y=0
        guard: x < 10
        body:
          x := x + 1
          y := y + 3
        """,
        """
        init: x=0, y=0
        guard: x < 10
        body:
          x := x + 1
          y := y + 1
        """,
        """
        init: x=0, y=10
        guard: x < 10
        body:
          x := x + 1
          y := y - 1
        """,
        """
        init: x=0, y=0
        guard: x < 10 and y < 20
        body:
          x := x + 1
          y := y + 2
        """,
        """
        init: x=10, y=0
        guard: x > 0
        body:
          x := x - 1
          y := y + 1
        """
    ]
    
    for i, code in enumerate(test_loops, 1):
        print(f"LOOP {i}")
        print("Source:")
        print(code.strip())
        print()
        
        loop = Loop.from_code(code)
        
        print("Linear Invariant Synthesis:")
        invariants = synthesize_linear_invariants(loop, max_total=8)
        
        if invariants:
            semantic = [inv for inv in invariants if inv.type == "==" or 
                       sum(1 for c in inv.coeffs.values() if c != 0) > 1]
            guard_dependent = [inv for inv in invariants if inv not in semantic]
            
            print(f"\n  Found {len(invariants)} linear invariant(s):")
            
            if semantic:
                print(f"\n    [Semantic Invariants - capture loop relationships]")
                for j, inv in enumerate(semantic[:3], 1):
                    print(f"      {j}. {inv.format()} [strength: {inv.strength_score}]")
            
            if guard_dependent and len(guard_dependent) <= 3:
                print(f"\n    [Guard-Dependent Invariants - derived from loop bounds]")
                for j, inv in enumerate(guard_dependent[:3], 1):
                    print(f"      {j}. {inv.format()} [strength: {inv.strength_score}]")
        else:
            print("\n  No linear invariants found")
        
        boolean_invariants = []
        if len(invariants) >= 2:
            boolean_invariants = synthesize_all_boolean_invariants(loop, invariants[:6], max_results=5)
            
            if boolean_invariants:
                print(f"\n  ✓ Top {len(boolean_invariants)} boolean invariant(s):")
                for j, bool_inv in enumerate(boolean_invariants, 1):
                    print(f"    {j}. [{bool_inv.structure}] {bool_inv.format()}")
                    print(f"       [strength: {bool_inv.strength_score}]")
        
        print("\n Termination Analysis:")
        ranking_fn = synthesize_ranking_function(loop)
        if ranking_fn:
            print(f"Ranking function: {ranking_fn.format()}")
        else:
            print(f"No ranking function found")
        
        if invariants or boolean_invariants or ranking_fn:
            print("\n  Generated Dafny Code:")
            dafny_code = generate_dafny_code(loop, invariants[:2], ranking_fn)
            for line in dafny_code.split('\n'):
                print(f"  {line}")