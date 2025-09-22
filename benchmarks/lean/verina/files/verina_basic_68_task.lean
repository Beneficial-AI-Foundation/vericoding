-- <vc-preamble>
import Mathlib

@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)

theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  sorry
-- </vc-theorems>