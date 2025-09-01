/- 
function_signature: "def how_many_times(string: str, substring: str) -> int"
docstring: |
  Find how many times a given substring can be found in the original string. Count overlaping cases.
test_cases:
  - input:
      - ""
      - "a"
    expected_output: 0
  - input:
      - "aaa"
      - "a"
    expected_output: 3
  - input:
      - "aaaa"
      - "aa"
    expected_output: 3
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) (substring: String) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → String → Nat)
-- inputs
(string substring: String) :=
-- spec
let spec (result: Nat) :=
(string.length < substring.length → result = 0)
∧
(string.length = substring.length →
((string = substring ↔ result = 1) ∧
(substring ≠ string ↔ result = 0)))
∧
(substring.length < string.length  →
let subtring_start_idx := {i: Nat | i ≤ string.length - substring.length};
let substring_occurrences := {i ∈ subtring_start_idx | (string.take (i + substring.length)).drop i = substring };
result = substring_occurrences.toFinset.card);
-- program termination
∃ result, implementation string substring = result ∧
spec result

theorem correctness
(string: String)
(substring: String)
: problem_spec implementation string substring
:=
-- <vc-proof>
  sorry
-- </vc-proof>

#test implementation "aaa" "a" = 3
#test implementation "aaaa" "aa" = 3
#test implementation "" "a" = 0
#test implementation "a" "" = 1
#test implementation "a" "a" = 1