/- 
function_signature: "def count_distinct_characters(string: str) -> int"
docstring: |
    Given a string, find out how many distinct characters (regardless of case) does it consist of
test_cases:
  - input: "xyzXYZ"
    expected_output: 3
  - input: "Jerry"
    expected_output: 4
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
-- spec
let spec (result: Nat) :=
let string_idx := {i: Nat | i < string.length}.toFinset
let characters := string_idx.image (fun i => string.toList[i]!)
let lowercase_characters := characters.image (fun c => c.toLower)
result = lowercase_characters.card;
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(string: String)
: problem_spec implementation string
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "xyzXYZ" = 3
-- #test implementation "Jerry" = 4