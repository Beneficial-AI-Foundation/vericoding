/- 
function_signature: "def concatenate(strings: List[str]) -> str"
docstring: |
    Concatenate list of strings into a single string
test_cases:
  - input: []
    expected_output: ""
  - input: ["a", "b", "c"]
    expected_output: "abc"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (strings: List String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List String → String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: String) :=
let result_chars := result.toList;
result_chars.length = (strings.map (λ s => s.length)).sum ∧
∀ i, i < strings.length →
(let string_in_result := strings.get! i;
let end_idx := ((strings.take (i + 1)).map (λ s => s.length)).sum;
let start_idx := end_idx - string_in_result.length;
let corresponding_string_in_result := ((result_chars.take end_idx).drop start_idx).asString;
corresponding_string_in_result = string_in_result);
-- program termination
∃ result, implementation strings = result ∧
spec result

theorem correctness
(strings: List String)
: problem_spec implementation strings
:=
-- <vc-proof>
  sorry
-- </vc-proof>

#test implementation [] = ""
#test implementation ["a", "b", "c"] = "abc"