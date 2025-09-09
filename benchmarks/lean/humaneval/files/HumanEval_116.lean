import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Nat) : List Nat :=
  sorry

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  ∀ x : Nat, lst.count x = result.count x ∧
  result.length = lst.length ∧
  (∀ i j : Nat, i < j → j < result.length →
    Nat.digits 2 (result[i]!) < Nat.digits 2 (result[j]!) ∨
    (Nat.digits 2 (result[i]!) = Nat.digits 2 (result[j]!) ∧ result[i]! < result[j]!))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  sorry

-- #test implementation [1, 5, 2, 3, 4] = [1, 2, 3, 4, 5]
-- #test implementation [1, 0, 2, 3, 4] = [0, 1, 2, 3, 4]