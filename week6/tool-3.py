from z3 import *
from typing import List, Dict, Optional, Tuple, Set
import re
from dataclasses import dataclass

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
                # extracting variables from guard
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
                        
                        # branching 
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
        # converting parsed loop to Z3 expressions
        z3_vars = {v: Int(v) for v in parsed.variables}
        
        guard_str = parsed.guard
        for var in parsed.variables:
            guard_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', guard_str)
        guard_z3 = eval(guard_str, {"z3_vars": z3_vars})
        
        updates = {}
        for item in parsed.body:
            if isinstance(item, Assignment):
                expr_str = item.expr
                for var in parsed.variables:
                    expr_str = re.sub(r'\b' + var + r'\b', f'z3_vars["{var}"]', expr_str)
                updates[item.var] = eval(expr_str, {"z3_vars": z3_vars})
            elif isinstance(item, Condition):
                # for now, handling simple conditionals by creating disjunctive updates
                # more complex: would need path-sensitive analysis
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

# loop rep 

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
        """
        normalizing coefficients to canonical form:
        1. Divide by GCD of all coefficients
        2. Make first non-zero coefficient positive
        """

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

        # not normalizing for inequalities to avoid flipping direction
    
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
        # dafny to invariant syntax! 
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
    s = Solver()
    coeffs = {v: Int(f"r_{v}") for v in loop.variables}
    
    for a in coeffs.values():
        s.add(a >= -10, a <= 10)
    
    s.add(Or([coeffs[v] != 0 for v in loop.variables]))
    
    z3_vars = loop.z3_vars
    
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

# ranking by strength 
def compute_strength(inv: Invariant, loop: Loop) -> int:
    score = 0
    
    #. equalities are the strongest
    if inv.type == "==":
        score += 100
    
    # penalty for large coefficients
    total_coeff_magnitude = sum(abs(c) for c in inv.coeffs.values())
    score -= total_coeff_magnitude
    
    # penalty for large constants
    score -= abs(inv.c) // 10
    
    # rewarding multi-variable invariants
    non_zero_coeffs = sum(1 for c in inv.coeffs.values() if c != 0)
    if non_zero_coeffs > 1:
        score += 20
    
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
    # verification 
    init_lhs = sum(inv.coeffs[v] * loop.init[v] for v in loop.variables)
    
    if inv.type == "==":
        if init_lhs != inv.c:
            return False
    else:  
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
        else:  # <=
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


# main pipeline for synthesis: 

def synthesize_linear_invariants(loop: Loop, max_total: int = 5) -> List[Invariant]:
    all_invariants = []
    
    print("[1/2] Searching for equality invariants")
    eq_invs = generate_all_invariants(loop, is_equality=True, max_candidates=5)
    all_invariants.extend(eq_invs)
    print(f"Found {len(eq_invs)} valid equality invariant(s)")
    
    print("[2/2] Searching for inequality invariants")
    ineq_invs = generate_all_invariants(loop, is_equality=False, max_candidates=5)
    all_invariants.extend(ineq_invs)
    print(f"Found {len(ineq_invs)} valid inequality invariant(s)")
    
    if not all_invariants:
        print("No valid invariants found")
    
    # rank 
    all_invariants.sort(key=lambda inv: inv.strength_score, reverse=True)
    
    return all_invariants[:max_total]


# dafny code generation! not perfectly working right now 

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

# main 

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
        init: x=0, y=0, z=0
        guard: x < 10
        body:
          x := x + 1
          if (x > 5) { z := z + 1 }
          y := y + 2
        """
    ]
    
    for i, code in enumerate(test_loops, 1):
        print(f"LOOP {i}")
        print("Source:")
        print(code.strip())
        print()
        
        loop = Loop.from_code(code)
        
        print("Synthesis Results:")
        invariants = synthesize_linear_invariants(loop, max_total=3)
        
        if invariants:
            print(f"\n Top {len(invariants)} invariant(s):")
            for j, inv in enumerate(invariants, 1):
                print(f" {j}. {inv.format()} [strength: {inv.strength_score}]")
        else:
            print("\n No invariants found")
        
        # not working correctly right now 
        print("\n  Termination Analysis:")
        ranking_fn = synthesize_ranking_function(loop)
        if ranking_fn:
            print(f"Ranking function: {ranking_fn.format()}")
        else:
            print(f"No ranking function found")
        
        # dafny code 
        if invariants or ranking_fn:
            print("\n  Generated Dafny Code:")
            dafny_code = generate_dafny_code(loop, invariants[:2], ranking_fn)
            for line in dafny_code.split('\n'):
                print(f" {line}")