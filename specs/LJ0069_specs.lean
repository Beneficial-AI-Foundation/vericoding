-- <vc-preamble>
-- Define Int bounds for the precondition
axiom Int.neg_div_two : Int
axiom Int.pos_div_two : Int
axiom Int.bounds_assumption : Int.neg_div_two < Int.pos_div_two

@[reducible, simp]
def maxDifference_precond (arr : Array Int) : Prop :=
  arr.size > 0 ∧ (∀ i, i < arr.size → Int.neg_div_two < arr[i]! ∧ arr[i]! < Int.pos_div_two)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxDifference (arr : Array Int) (h_precond : maxDifference_precond arr) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxDifference_postcond (arr : Array Int) (diff: Int) (h_precond : maxDifference_precond arr) : Prop :=
  ∀ i j, i < arr.size → j < arr.size → arr[i]! - arr[j]! ≤ diff

theorem maxDifference_spec_satisfied (arr: Array Int) (h_precond : maxDifference_precond arr) :
    maxDifference_postcond arr (maxDifference arr h_precond) h_precond := by
  sorry
-- </vc-theorems>