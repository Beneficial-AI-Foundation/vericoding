import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (arr: List Int) : Bool :=
  sorry

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(arr: List Int) :=
let is_shifted (xs: List Int) (ys: List Int) (i: Nat) :=
  (xs.length = ys.length) ∧
  (0 <= i) ∧
  (i < xs.length) ∧
  (forall j, (0 <= j ∧ j < ys.length) → (ys[j]! = xs[(j-i) % xs.length]!))
-- spec
let spec (result: Bool) :=
  ((arr = []) → (result = True)) ∧
  result ↔ (exists i, exists arr_shifted, (is_shifted arr arr_shifted i) ∧ (List.Sorted Int.le arr_shifted))
-- program termination
∃ result, implementation arr = result ∧
spec result

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= by
  sorry

-- #test implementation [3, 4, 5, 1, 2] = True
-- #test implementation [3, 5, 10, 1, 2] = True
-- #test implementation [4, 3, 1, 2] = False
-- #test implementation [3, 5, 4, 1, 2] = False
-- #test implementation [] = True