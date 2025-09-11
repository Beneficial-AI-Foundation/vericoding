-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (lst: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.Prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst[i]!) ∧
    (∀ j, j < lst.length ∧ Prime (lst[j]!) → lst[i]! ≤ lst[j]!) ∧
    result = (Nat.digits 10 (lst[i]!)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  sorry
-- </vc-theorems>

-- #test implementation [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3] = 10
-- #test implementation [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1] = 25
-- #test implementation [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3] = 13
-- #test implementation [0,724,32,71,99,32,6,0,5,91,83,0,5,6] = 11
-- #test implementation [0,81,12,3,1,21] = 3
-- #test implementation [0,8,1,2,1,7] = 7