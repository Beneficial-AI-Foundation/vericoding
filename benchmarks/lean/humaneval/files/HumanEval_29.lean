/- 
function_signature: "def filter_by_prefix(strings: List[str], prefix: str) -> List[str]"
docstring: |
    Filter an input list of strings only for ones that start with a given prefix.
test_cases:
  - input:
    - []
    - "a"
    expected_output: []
  - input:
    - ["abc", "bcd", "cde", "array"]
    - "a"
    expected_output: ["abc", "array"]
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (strings: List String) (pref: String) : List String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List String → String → List String)
-- inputs
(strings: List String)
(pref: String) :=
-- spec
let spec (result: List String) :=
result.all (λ s => s.startsWith pref) ∧
result.all (λ s => s ∈ strings) ∧
strings.all (λ s => s.startsWith pref → s ∈ result) ∧
∀ s : String, s ∈ result → result.count s = strings.count s;
-- program termination
∃ result, implementation strings pref = result ∧
spec result

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref
:=
-- <vc-proof>
  sorry
-- </vc-proof>

#test implementation [] "a" = []
#test implementation ["abc", "bcd", "cde", "array"] "a" = ["abc", "array"]