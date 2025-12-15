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


class QuadraticInvariant:
    
    def __init__(self, quad_coeffs, linear_coeffs, constant, inv_type, strength_score=0):
        self.quad_coeffs = quad_coeffs
        self.linear_coeffs = linear_coeffs
        self.constant = constant
        self.type = inv_type
        self.strength_score = strength_score
        self._normalize()
    
    def _normalize(self):
        from math import gcd
        from functools import reduce
        
        all_coeffs = (list(self.quad_coeffs.values()) + 
                     list(self.linear_coeffs.values()) + 
                     [self.constant])
        non_zero = [abs(c) for c in all_coeffs if c != 0]
        
        if not non_zero:
            return
        
        g = reduce(gcd, non_zero)
        if g > 1:
            self.quad_coeffs = {k: v // g for k, v in self.quad_coeffs.items()}
            self.linear_coeffs = {k: v // g for k, v in self.linear_coeffs.items()}
            self.constant = self.constant // g
        
        normalized_quad = {}
        for (v1, v2), coef in self.quad_coeffs.items():
            if v1 == v2:
                normalized_quad[(v1, v2)] = coef
            else:
                key = tuple(sorted([v1, v2]))
                normalized_quad[key] = normalized_quad.get(key, 0) + coef
        self.quad_coeffs = normalized_quad
    
    def format(self):
        terms = []
        
        for (v1, v2) in sorted(self.quad_coeffs.keys()):
            coef = self.quad_coeffs[(v1, v2)]
            if coef == 0:
                continue
            
            if v1 == v2:
                var_str = f"{v1}²"
            else:
                var_str = f"{v1}*{v2}"
            
            if len(terms) == 0:
                if coef == 1:
                    terms.append(var_str)
                elif coef == -1:
                    terms.append(f"-{var_str}")
                else:
                    terms.append(f"{coef}*{var_str}")
            else:
                if coef > 0:
                    if coef == 1:
                        terms.append(f" + {var_str}")
                    else:
                        terms.append(f" + {coef}*{var_str}")
                else:
                    if coef == -1:
                        terms.append(f" - {var_str}")
                    else:
                        terms.append(f" - {abs(coef)}*{var_str}")
        
        for var in sorted(self.linear_coeffs.keys()):
            coef = self.linear_coeffs[var]
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
        return f"{lhs} {self.type} {self.constant}"
    
    def to_dafny(self) -> str:
        terms = []
        
        for (v1, v2) in sorted(self.quad_coeffs.keys()):
            coef = self.quad_coeffs[(v1, v2)]
            if coef == 0:
                continue
            
            if v1 == v2:
                if coef == 1:
                    terms.append(f"({v1} * {v1})")
                elif coef == -1:
                    terms.append(f"(-({v1} * {v1}))")
                else:
                    terms.append(f"({coef} * {v1} * {v1})")
            else:
                # Cross term
                if coef == 1:
                    terms.append(f"({v1} * {v2})")
                elif coef == -1:
                    terms.append(f"(-({v1} * {v2}))")
                else:
                    terms.append(f"({coef} * {v1} * {v2})")
        
        for var in sorted(self.linear_coeffs.keys()):
            coef = self.linear_coeffs[var]
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
        return f"invariant {lhs} {op} {self.constant}"
    
    def to_z3(self, z3_vars: Dict[str, Any]):
        lhs = 0
        
        for (v1, v2), coef in self.quad_coeffs.items():
            if coef == 0:
                continue
            lhs += coef * z3_vars[v1] * z3_vars[v2]
        
        for var, coef in self.linear_coeffs.items():
            if coef == 0:
                continue
            lhs += coef * z3_vars[var]
        
        if self.type == "==":
            return lhs == self.constant
        else:
            return lhs <= self.constant

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
        expr = ""
        if hasattr(self, 'bound') and self.bound is not None and self.bound != 0:
            expr = str(self.bound)

        for var in sorted(self.coeffs.keys()):
            coef = self.coeffs[var]
            if coef == 0:
                continue
            term = var if abs(coef) == 1 else f"{abs(coef)}*{var}"
            if expr == "":
                expr = (f"-{term}" if coef < 0 else f"{term}")
            else:
                expr += (f" - {term}" if coef < 0 else f" + {term}")

        return expr if expr != "" else "0"

def synthesize_ranking_function(loop: Loop) -> Optional[RankingFunction]:
    result = _try_linear_ranking(loop)
    if result:
        return result
    
    result = _try_linear_ranking(loop, relax_bounds=True)
    if result:
        return result
    
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


def sample_reachable_states(loop: Loop, max_steps: int = 30) -> List[Dict[str, int]]:
    states = []
    state = {v: loop.init[v] for v in loop.variables}
    states.append(state.copy())
    for _ in range(max_steps):
        if not eval_z3_expr(loop.guard, state):
            break
        state = eval_updates(loop.updates, state, loop.z3_vars)
        states.append(state.copy())
    return states


def generate_quadratic_invariants_sampling(loop: Loop, is_equality: bool, max_candidates: int = 5) -> List[QuadraticInvariant]:
    vars = list(loop.variables)
    monomials = []
    for i, v1 in enumerate(vars):
        for v2 in vars[i:]:
            monomials.append((v1, v2))

    samples = sample_reachable_states(loop, max_steps=30)
    if len(samples) < 3:
        return []

    s = Solver()
    coeffs = {m: Int(f'sq_{m[0]}_{m[1]}') for m in monomials}
    lin = {v: Int(f'sl_{v}') for v in vars}
    const = Int('sk')

    for v in coeffs.values():
        s.add(v >= -20, v <= 20)
    for v in lin.values():
        s.add(v >= -50, v <= 50)
    s.add(const >= -200, const <= 200)

    s.add(Or([coeffs[m] != 0 for m in coeffs] + [lin[v] != 0 for v in lin]))

    for st in samples:
        expr = const
        for (v1, v2), coef_var in coeffs.items():
            expr = expr + coef_var * (st[v1] * st[v2])
        for v, coef_var in lin.items():
            expr = expr + coef_var * st[v]
        if is_equality:
            s.add(expr == 0)
        else:
            s.add(expr <= 0)

    candidates: List[QuadraticInvariant] = []
    attempts = 0
    max_attempts = max_candidates * 3
    seen = set()
    while len(candidates) < max_candidates and attempts < max_attempts:
        attempts += 1
        if s.check() != sat:
            break
        m = s.model()
        quad_vals = {mkey: m[coef].as_long() for mkey, coef in coeffs.items()}
        lin_vals = {v: m[lin[v]].as_long() for v in vars}
        const_val = m[const].as_long()

        inv = QuadraticInvariant(quad_vals, lin_vals, const_val, '==' if is_equality else '<=')
        if verify_quadratic_invariant(inv, loop):
            sig = (tuple(sorted(inv.quad_coeffs.items())), tuple(sorted(inv.linear_coeffs.items())), inv.constant, inv.type)
            if sig not in seen:
                candidates.append(inv)
                seen.add(sig)

        block = []
        for coef_var in list(coeffs.values()) + list(lin.values()) + [const]:
            block.append(coef_var != m[coef_var])
        s.add(Or(block))

    return candidates

def quadratic_template(vars):
    quad_coeffs = {}
    
    for v in vars:
        quad_coeffs[(v, v)] = Int(f"q_{v}_{v}")
    
    for i, v1 in enumerate(vars):
        for v2 in vars[i+1:]:
            quad_coeffs[(v1, v2)] = Int(f"q_{v1}_{v2}")
    
    linear_coeffs = {v: Int(f"l_{v}") for v in vars}
    
    constant = Int("k")
    
    return quad_coeffs, linear_coeffs, constant


def quadratic_initialization_constraint(quad_coeffs, linear_coeffs, constant, loop, is_equality):
    lhs = 0
    
    for (v1, v2), coef in quad_coeffs.items():
        lhs += coef * loop.init[v1] * loop.init[v2]
    
    for v, coef in linear_coeffs.items():
        lhs += coef * loop.init[v]
    
    return lhs == constant if is_equality else lhs <= constant


def quadratic_preservation_constraint(quad_coeffs, linear_coeffs, constant, loop, is_equality):
    z3_vars = loop.z3_vars
    
    lhs_curr = 0
    for (v1, v2), coef in quad_coeffs.items():
        lhs_curr += coef * z3_vars[v1] * z3_vars[v2]
    for v, coef in linear_coeffs.items():
        lhs_curr += coef * z3_vars[v]
    
    inv_curr = (lhs_curr == constant) if is_equality else (lhs_curr <= constant)
    
    lhs_next = 0
    for (v1, v2), coef in quad_coeffs.items():
        lhs_next += coef * loop.updates[v1] * loop.updates[v2]
    for v, coef in linear_coeffs.items():
        lhs_next += coef * loop.updates[v]
    
    inv_next = (lhs_next == constant) if is_equality else (lhs_next <= constant)
    
    return ForAll(
        list(z3_vars.values()),
        Implies(And(inv_curr, loop.guard), inv_next)
    )


def compute_quadratic_strength(inv: QuadraticInvariant, loop: Loop) -> int:
    score = 0
    
    if inv.type == "==":
        score += 2000
    
    num_quad_terms = sum(1 for c in inv.quad_coeffs.values() if c != 0)
    num_linear_terms = sum(1 for c in inv.linear_coeffs.values() if c != 0)
    
    score -= (num_quad_terms * 50 + num_linear_terms * 20)
    
    total_quad_magnitude = sum(abs(c) for c in inv.quad_coeffs.values())
    total_linear_magnitude = sum(abs(c) for c in inv.linear_coeffs.values())
    score -= (total_quad_magnitude * 15 + total_linear_magnitude * 10)
    
    score -= abs(inv.constant) * 5
    
    if num_quad_terms > 0 and num_linear_terms > 0:
        score += 300

    if num_quad_terms > 0 and num_linear_terms == 0:
        score += 200
    
    return score


def generate_quadratic_invariants(loop: Loop, is_equality: bool, 
                                  max_candidates: int = 10) -> List[QuadraticInvariant]:
    s = Solver()
    s.set("timeout", 30000)  
    
    quad_coeffs, linear_coeffs, constant = quadratic_template(loop.variables)
    
    for coef in quad_coeffs.values():
        s.add(coef >= -5, coef <= 5)
    for coef in linear_coeffs.values():
        s.add(coef >= -10, coef <= 10)
    s.add(constant >= -50, constant <= 50)
    
    s.add(Or([quad_coeffs[k] != 0 for k in quad_coeffs.keys()]))
    
    s.add(quadratic_initialization_constraint(quad_coeffs, linear_coeffs, constant, loop, is_equality))
    s.add(quadratic_preservation_constraint(quad_coeffs, linear_coeffs, constant, loop, is_equality))
    
    candidates = []
    seen_normalized = set()
    attempts = 0
    max_attempts = max_candidates * 3
    
    while len(candidates) < max_candidates and attempts < max_attempts:
        attempts += 1
        
        if s.check() == sat:
            m = s.model()
            
            inv = QuadraticInvariant(
                quad_coeffs={k: m[v].as_long() for k, v in quad_coeffs.items()},
                linear_coeffs={k: m[v].as_long() for k, v in linear_coeffs.items()},
                constant=m[constant].as_long(),
                inv_type="==" if is_equality else "<="
            )
            
            if verify_quadratic_invariant(inv, loop):
                if is_globally_valid_quadratic(inv):
                    blocking = []
                    for k, v in quad_coeffs.items():
                        blocking.append(v != m[v])
                    for k, v in linear_coeffs.items():
                        blocking.append(v != m[v])
                    blocking.append(constant != m[constant])
                    s.add(Or(blocking))
                    continue
                
                if not check_violated_by_relaxation(inv, loop):
                    inv.strength_score = compute_quadratic_strength(inv, loop) - 500
                else:
                    inv.strength_score = compute_quadratic_strength(inv, loop)
                
                norm_sig = (
                    tuple(sorted(inv.quad_coeffs.items())),
                    tuple(sorted(inv.linear_coeffs.items())),
                    inv.constant,
                    inv.type
                )
                
                if norm_sig not in seen_normalized:
                    candidates.append(inv)
                    seen_normalized.add(norm_sig)
            
            blocking = []
            for k, v in quad_coeffs.items():
                blocking.append(v != m[v])
            for k, v in linear_coeffs.items():
                blocking.append(v != m[v])
            blocking.append(constant != m[constant])
            s.add(Or(blocking))
        else:
            break
    
    if len(candidates) == 0:
        sampling_cands = generate_quadratic_invariants_sampling(loop, is_equality, max_candidates=max_candidates)
        for inv in sampling_cands:
            norm_sig = (
                tuple(sorted(inv.quad_coeffs.items())),
                tuple(sorted(inv.linear_coeffs.items())),
                inv.constant,
                inv.type,
            )
            if norm_sig not in seen_normalized:
                candidates.append(inv)
                seen_normalized.add(norm_sig)

    return candidates


def verify_quadratic_invariant(inv: QuadraticInvariant, loop: Loop) -> bool:
    init_lhs = 0
    for (v1, v2), coef in inv.quad_coeffs.items():
        init_lhs += coef * loop.init[v1] * loop.init[v2]
    for v, coef in inv.linear_coeffs.items():
        init_lhs += coef * loop.init[v]
    
    if inv.type == "==":
        if init_lhs != inv.constant:
            return False
    else:
        if init_lhs > inv.constant:
            return False
    
    state = {v: loop.init[v] for v in loop.variables}
    
    for iteration in range(min(10, 50)):
        guard_holds = eval_z3_expr(loop.guard, state)
        if not guard_holds:
            break
        
        lhs = 0
        for (v1, v2), coef in inv.quad_coeffs.items():
            lhs += coef * state[v1] * state[v2]
        for v, coef in inv.linear_coeffs.items():
            lhs += coef * state[v]
        
        if inv.type == "==":
            if lhs != inv.constant:
                return False
        else:
            if lhs > inv.constant:
                return False
        
        state = eval_updates(loop.updates, state, loop.z3_vars)
    
    return True


def is_globally_valid_quadratic(inv: QuadraticInvariant) -> bool:
    test_vars = {v: Int(f"test_{v}") for v in inv.linear_coeffs.keys()}
    
    lhs = 0
    for (v1, v2), coef in inv.quad_coeffs.items():
        if coef != 0:
            lhs += coef * test_vars[v1] * test_vars[v2]
    for v, coef in inv.linear_coeffs.items():
        if coef != 0:
            lhs += coef * test_vars[v]

    s = Solver()
    s.set("timeout", 5000) 
    
    if inv.type == "==":
        s.add(lhs != inv.constant)
    else:  # "<="
        s.add(lhs > inv.constant)
    
    result = s.check()
    
    if result == unsat:
        return True

    if inv.type == "<=" and inv.constant >= 0:
        all_non_positive = True
        for (v1, v2), coef in inv.quad_coeffs.items():
            if v1 == v2 and coef > 0:  # Positive diagonal term
                all_non_positive = False
                break
        
        if all_non_positive and inv.constant >= 0:
            test_points = [
                {v: val for v, val in zip(sorted(test_vars.keys()), point)}
                for point in [(0, 0), (1, 1), (-1, -1), (10, 10), (100, -100)]
            ]
            
            holds_everywhere = True
            for point in test_points:
                val = 0
                for (v1, v2), coef in inv.quad_coeffs.items():
                    val += coef * point.get(v1, 0) * point.get(v2, 0)
                for v, coef in inv.linear_coeffs.items():
                    val += coef * point.get(v, 0)
                
                if val > inv.constant:
                    holds_everywhere = False
                    break
            
            if holds_everywhere:
                return True
    
    return False


def check_violated_by_relaxation(inv: QuadraticInvariant, loop: Loop) -> bool:
    s = Solver()
    s.set("timeout", 5000)
    
    z3_vars = loop.z3_vars
    
    inv_expr = inv.to_z3(z3_vars)
    
    guard_str = str(loop.guard)
    relaxed_constraints = []
    
    for var in loop.variables:
        import re
        matches = re.findall(rf'{var}\s*<\s*(\d+)', guard_str)
        if matches:
            bound = int(matches[0])
            relaxed_constraints.append(z3_vars[var] < 2 * bound)
            relaxed_constraints.append(z3_vars[var] >= -bound)
        
        matches = re.findall(rf'{var}\s*>\s*(\d+)', guard_str)
        if matches:
            bound = int(matches[0])
            relaxed_constraints.append(z3_vars[var] > bound // 2)
            relaxed_constraints.append(z3_vars[var] <= 2 * bound)
        
        if not re.search(rf'{var}\s*[<>]', guard_str):
            relaxed_constraints.append(z3_vars[var] >= -100)
            relaxed_constraints.append(z3_vars[var] <= 100)
    
    if relaxed_constraints:
        s.add(And(relaxed_constraints))
    
    s.add(Not(inv_expr))
    
    result = s.check()

    return result == sat

def synthesize_quadratic_invariants(loop: Loop, max_total: int = 5) -> List[QuadraticInvariant]:
    all_invariants = []
    
    print("  [1/2] Searching for quadratic equality invariants...")
    eq_invs = generate_quadratic_invariants(loop, is_equality=True, max_candidates=5)
    all_invariants.extend(eq_invs)
    print(f"        Found {len(eq_invs)} valid quadratic equality invariant(s)")
    
    print("  [2/2] Searching for quadratic inequality invariants...")
    ineq_invs = generate_quadratic_invariants(loop, is_equality=False, max_candidates=5)
    all_invariants.extend(ineq_invs)
    print(f"        Found {len(ineq_invs)} valid quadratic inequality invariant(s)")
    
    if not all_invariants:
        print("        No valid quadratic invariants found")
    
    all_invariants.sort(key=lambda inv: inv.strength_score, reverse=True)
    
    return all_invariants[:max_total]

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

def generate_dafny_code(loop: Loop, invariants: List[Invariant], ranking_fn: Optional[RankingFunction], quad_invariants: List[QuadraticInvariant] = None) -> str:
    
    code = f"method LoopExample()\n{{\n"

    for var in sorted(loop.variables):
        init_val = loop.init.get(var, 0)
        code += f"  var {var}: int := {init_val};\n"

    code += f"\n"
    
    # Convert Z3 guard to Dafny-friendly infix boolean expressions
    import re
    guard_str = str(loop.guard)
    guard_str = guard_str.replace("Not", "!").replace("And", "&&").replace("Or", "||")

    def _fix_bool_lists(s: str, op: str) -> str:
        pattern = re.compile(re.escape(op) + r"\(([^()]+)\)")
        while True:
            m = pattern.search(s)
            if not m:
                break
            inner = m.group(1)
            parts = [p.strip() for p in inner.split(',')]
            repl = '(' + f' {op} '.join(parts) + ')'
            s = s[:m.start()] + repl + s[m.end():]
        return s

    guard_str = _fix_bool_lists(guard_str, '&&')
    guard_str = _fix_bool_lists(guard_str, '||')

    for var in loop.variables:
        guard_str = guard_str.replace(f"{var}", var)
    
    code += f"  while ({guard_str})\n"
    
    for inv in invariants:
        code += f"    {inv.to_dafny()}\n"

    if quad_invariants:
        for inv in quad_invariants:
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
    
    # close loop and method
    code += f"  }}\n"
    code += f"}}\n"

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
    
    quadratic_test_loops = [
        """
        init: x=1, y=1
        guard: x < 100
        body:
          x := x + y
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
        guard: x < 5
        body:
          x := x + 1
          y := 2 * y + 1
        """,
    ]
    
    print("\n" + "="*80)
    print("QUADRATIC INVARIANT SYNTHESIS TESTS")
    print("="*80 + "\n")
    
    for i, code in enumerate(quadratic_test_loops, 1):
        print(f"\n{'='*80}")
        print(f"QUADRATIC TEST LOOP {i}")
        print('='*80)
        print("Source:")
        print(code.strip())
        print()
        
        loop = Loop.from_code(code)
        
        print("Quadratic Invariant Synthesis:")
        quad_invariants = synthesize_quadratic_invariants(loop, max_total=5)
        
        if quad_invariants:
            print(f"\n  ✓ Found {len(quad_invariants)} quadratic invariant(s):")
            for j, inv in enumerate(quad_invariants, 1):
                print(f"    {j}. {inv.format()}")
                print(f"       [strength: {inv.strength_score}]")
                print(f"       Dafny: {inv.to_dafny()}")
        else:
            print("\n  No quadratic invariants found")
        
        print("\n" + "-"*80)

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
            try:
                import re
                guard_s = str(loop.guard)
                m = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*<\s*(\d+)", guard_s)
                if m:
                    gv = m.group(1)
                    gb = int(m.group(2))
                    update_expr = str(loop.updates.get(gv, ""))
                    if gv in loop.updates and (f"{gv} + " in update_expr or f"{gv}+" in update_expr):
                        print(f"Heuristic decreases: {gb} - {gv}")
                    else:
                        print(f"No ranking function found")
                else:
                    print(f"No ranking function found")
            except Exception:
                print(f"No ranking function found")
        
        if invariants or boolean_invariants or ranking_fn:
            print("\n  Generated Dafny Code:")
            dafny_code = generate_dafny_code(loop, invariants[:2], ranking_fn)
            for line in dafny_code.split('\n'):
                print(f"  {line}")