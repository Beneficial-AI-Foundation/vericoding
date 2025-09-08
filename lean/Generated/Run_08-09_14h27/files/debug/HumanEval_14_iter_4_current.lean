/- 
function_signature: "def all_prefixes(string: str) -> List[str]"
docstring: |
    Return list of all prefixes from shortest to longest of the input string
test_cases:
  - input: "abc"
    expected_output:
      - "a"
      - "ab"
      - "abc"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : List String :=
  (List.range string.length).map (fun i => string.take (i + 1))

def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(string: String) :=
-- spec
let spec (result: List String) :=
result.length = string.length ∧
∀ i, i < result.length →
result[i]! = string.take (i + 1);
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec
  use (List.range string.length).map (fun i => string.take (i + 1))
  constructor
  · rfl
  · constructor
    · simp [List.length_map, List.length_range]
    · intro i hi
      simp [List.getElem_map]
      simp [List.getElem_range]

-- #test implementation "abc" = ["a", "ab", "abc"]