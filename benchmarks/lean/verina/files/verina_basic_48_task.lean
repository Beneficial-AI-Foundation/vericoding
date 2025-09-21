-- <vc-preamble>
import Mathlib

@[reducible, simp]
def isPerfectSquare_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPerfectSquare (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isPerfectSquare_postcond (n : Nat) (result : Bool) : Prop :=
  result ↔ ∃ i : Nat, i * i = n

theorem isPerfectSquare_spec_satisfied (n : Nat) :
    isPerfectSquare_postcond n (isPerfectSquare n) := by
  sorry
-- </vc-theorems>