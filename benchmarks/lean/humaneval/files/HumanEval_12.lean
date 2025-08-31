/- 
function_signature: "def longest(strings: List[str]) -> Optional[str]"
docstring: |
    Out of list of strings, return the longest one. Return the first one in case of multiple
    strings of the same length. Return None in case the input list is empty.
test_cases:
  - input: []
    expected_output: None
  - input: ["a", "b", "c"]
    expected_output: "a"
  - input: ["a", "bb", "ccc"]
    expected_output: "ccc"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (strings: List String) : Option String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List String → Option String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: Option String) :=
  (result = none ↔ strings.length = 0) ∨
  (∃ longest, result = some longest ∧
  longest ∈ strings ∧
  ∀ s, s ∈ strings → s.length ≤ longest.length →
  (∃ i, i < strings.length ∧
  strings[i]! = longest ∧ ∀ j < i, strings[j]!.length < longest.length));
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

#test implementation ["a", "b", "c"] = some "a"
#test implementation ["a", "bb", "ccc"] = some "ccc"
#test implementation [] = none