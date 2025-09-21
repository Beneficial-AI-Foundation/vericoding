-- <vc-preamble>
import Mathlib

def swapFirstAndLast_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swapFirstAndLast (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
-- Theorem: The last element of the input array should be the first element of the modified array; The first element of the input array should be the last element of the modified array; All other elements remain unchanged
@[reducible, simp]
def swapFirstAndLast_postcond (a : Array Int) (result : Array Int) (h_precond: swapFirstAndLast_precond a) : Prop :=
  result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)

theorem swapFirstAndLast_spec_satisfied (a : Array Int) (h_precond: swapFirstAndLast_precond a) :
    swapFirstAndLast_postcond a (swapFirstAndLast a h_precond) h_precond := by
  sorry
-- </vc-theorems>