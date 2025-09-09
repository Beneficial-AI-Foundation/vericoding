import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (s: String) : Bool :=
  sorry

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

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  sorry

-- #test implementation "a" = False
-- #test implementation "aa" = False
-- #test implementation "abcd" = True
-- #test implementation "aabb" = False
-- #test implementation "adb" = True