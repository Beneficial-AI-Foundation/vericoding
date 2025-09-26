import Mathlib
-- <vc-preamble>
@[reducible, simp]
def reverseToK_precond (list : Array Int) (n : Nat) : Prop :=
  list.size > 0 ∧ 0 < n ∧ n < list.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def reverseToK (list : Array Int) (n : Nat) (h_precond : reverseToK_precond list n) : Array Int :=
  ((list.toList.take n).reverse ++ (list.toList.drop n)).toArray
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def reverseToK_postcond (list : Array Int) (n : Nat) (result : Array Int) (h_precond : reverseToK_precond list n) : Prop :=
  result.toList = (list.toList.take n).reverse ++ (list.toList.drop n)

theorem reverseToK_spec_satisfied (list : Array Int) (n : Nat) (h_precond : reverseToK_precond list n) :
    reverseToK_postcond list n (reverseToK list n h_precond) h_precond := by
  simp [reverseToK_postcond, reverseToK]
-- </vc-theorems>
