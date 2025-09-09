import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
  result ↔
  (3 ≤ s.length) ∧
  ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data[i]! = s.data[j]!)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
/-
function_signature: "def is_happy(s: str) -> bool"
docstring: |
    You are given a string s.
    Your task is to check if the string is happy or not.
    A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
test_cases:
  - input: "a"
    output: False
  - input: "aa"
    output: False
  - input: "abcd"
    output: True
  - input: "aabb"
    output: False
  - input: "adb"
    output: True
-/
-- </vc-description>

-- <vc-spec>
def implementation (s: String) : Bool :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(s: String)
: problem_spec implementation s
:=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation "a" = False
-- #test implementation "aa" = False
-- #test implementation "abcd" = True
-- #test implementation "aabb" = False
-- #test implementation "adb" = True