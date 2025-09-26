import Mathlib
-- <vc-preamble>
-- Function to compute sum of negative numbers from sequence recursively
def sum_negative_to (seq : List Int) : Int :=
  match seq with
  | [] => 0
  | h :: t => sum_negative_to t + if h < 0 then h else 0

@[reducible, simp]
def sumNegatives_precond (arr : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma sum_negative_to_nil : sum_negative_to ([] : List Int) = 0 := rfl
-- LLM HELPER
@[simp] lemma sum_negative_to_cons (h : Int) (t : List Int) :
  sum_negative_to (h :: t) = sum_negative_to t + if h < 0 then h else 0 := rfl
-- </vc-helpers>

-- <vc-definitions>
def sumNegatives (arr : Array Int) (h_precond : sumNegatives_precond (arr)) : Int :=
  sum_negative_to (arr.toList)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sumNegatives_postcond (arr : Array Int) (sum_neg: Int) (h_precond : sumNegatives_precond (arr)) :=
  sum_negative_to (arr.toList) = sum_neg

theorem sumNegatives_spec_satisfied (arr: Array Int) (h_precond : sumNegatives_precond (arr)) :
    sumNegatives_postcond (arr) (sumNegatives (arr) h_precond) h_precond := by
  simp [sumNegatives_postcond, sumNegatives]
-- </vc-theorems>
