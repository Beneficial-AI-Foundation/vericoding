import Mathlib
-- <vc-preamble>
@[reducible, simp]
def removeKthElement_precond (list : Array Int) (k : Nat) :=
  list.size > 0 ∧ 0 < k ∧ k < list.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma list_toArray_toList_int (l : List Int) : l.toArray.toList = l := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def removeKthElement (list : Array Int) (k : Nat) (h_precond : removeKthElement_precond list k) : Array Int :=
  (list.toList.take (k - 1) ++ list.toList.drop k).toArray
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeKthElement_postcond (list : Array Int) (k : Nat) (new_list : Array Int) (h_precond : removeKthElement_precond list k) :=
  new_list.toList = (list.toList.take (k - 1)) ++ (list.toList.drop k)

theorem removeKthElement_spec_satisfied (list : Array Int) (k : Nat) (h_precond : removeKthElement_precond list k) :
    removeKthElement_postcond list k (removeKthElement list k h_precond) h_precond := by
  simp [removeKthElement_postcond, removeKthElement]
-- </vc-theorems>
