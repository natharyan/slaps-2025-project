import re
import json

class DafnyParser:
    def __init__(self, code: str):
        self.code = code

    def parse_method_signature(self):
        method_pattern = re.compile(r"method\s+(\w+)\s*\((.*?)\)\s*returns\s*\((.*?)\)", re.DOTALL)
        match = method_pattern.search(self.code)
        if not match: return None
        name, params, rets = match.groups()
        return name, self._parse_params(params), self._parse_params(rets)

    def _parse_params(self, s):
        res = []
        for p in s.split(","):
            if ":" in p:
                n, t = p.split(":")
                res.append({"name": n.strip(), "type": t.strip()})
        return res

    def parse_conditions(self, keyword: str):
        pattern = re.compile(rf"{keyword}\s+([^\n]+)")
        return [c.strip().rstrip('{').strip() for c in pattern.findall(self.code)]

    def parse_loops(self):
        loops = []
        loop_iterator = re.finditer(r"\b(while|for)\b", self.code)
        
        for match in loop_iterator:
            loop_type = match.group(1)
            start_index = match.start()
            
            post_loop = self.code[match.end():]
            brace_pos = post_loop.find("{")
            header = post_loop[:brace_pos]
            
            body_content = ""
            brace_count = 0
            absolute_brace_start = match.end() + brace_pos
            for i, char in enumerate(self.code[absolute_brace_start:]):
                if char == "{": brace_count += 1
                elif char == "}": brace_count -= 1
                if brace_count == 0:
                    body_content = self.code[absolute_brace_start + 1 : absolute_brace_start + i]
                    break
            
            invariants = [inv.strip() for inv in re.findall(r"invariant\s+([^;\n{]+)", header)]
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
                condition = cond_match.group(1).strip().strip("()")
                variables = self._extract_variables(condition, body_content)

            loops.append({
                "type": loop_type,
                "condition": condition,
                "variables": variables,
                "invariants": invariants
            })
        return loops

    def _extract_variables(self, condition: str, body: str) -> list:
        assigned = re.findall(r"\b(\w+)\s* :=", body)
        in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
        
        all_vars = set(assigned + in_cond)
        keywords = {"while", "for", "if", "else", "invariant", "var", "n", "true", "false", "to"} 
        return sorted([v for v in all_vars if v not in keywords and not v.isdigit()])

    def parse(self):
        sig = self.parse_method_signature()
        if not sig: return {}
        name, params, rets = sig
        return {
            "method_name": name,
            "loops": self.parse_loops(),
            "preconditions": self.parse_conditions("requires"),
            "postconditions": self.parse_conditions("ensures"),
            "parameters": params,
            "returns": rets
        }


dafny_input = """
method Sum(n: int) returns (result: int)
  requires n >= 0
  ensures result == n * (n + 1) / 2
{
  var i := 0;
  var sum := 0;
  
  while (i <= n)
    invariant 0 <= i <= n + 1
    invariant sum == i * (i - 1) / 2
  {
    sum := sum + i;
    i := i + 1;
  }
  
  result := sum;
}


"""

parser = DafnyParser(dafny_input)
output = parser.parse()

# for_loop was saved under for_loop.json 
output_file = "simple_loop.json"
with open(output_file, "w") as f:
    json.dump(output, f, indent=2)

print(f"Parser output written to {output_file}")
