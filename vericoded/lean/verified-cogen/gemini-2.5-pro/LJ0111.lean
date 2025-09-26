import Mathlib
-- <vc-preamble>
@[reducible, simp]
def removeKthElement_precond (list : Array Int) (k : Nat) :=
  list.size > 0 ∧ 0 < k ∧ k < list.size
-- </vc-preamble>

-- <vc-helpers>
theorem Array_extract_append_toList_equiv_List_take_drop (l : Array Int) (k : Nat) (h : k < l.size) :
  ((l.extract 0 (k - 1)) ++ (l.extract k l.size)).toList = l.toList.take (k - 1) ++ l.toList.drop k := by
  simp [Array.toList_append, Array.toList_extract, List.length_drop]
-- </vc-helpers>

-- <vc-definitions>
def removeKthElement (list : Array Int) (k : Nat) (h_precond : removeKthElement_precond list k) : Array Int :=
  list.extract 0 (k - 1) ++ list.extract k list.size
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeKthElement_postcond (list : Array Int) (k : Nat) (new_list : Array Int) (h_precond : removeKthElement_precond list k) :=
  new_list.toList = (list.toList.take (k - 1)) ++ (list.toList.drop k)

theorem removeKthElement_spec_satisfied (list : Array Int) (k : Nat) (h_precond : removeKthElement_precond list k) :
    removeKthElement_postcond list k (removeKthElement list k h_precond) h_precond := by
  simp only [removeKthElement_postcond, removeKthElement]
  apply Array_extract_append_toList_equiv_List_take_drop
  exact h_precond.2.2
-- </vc-theorems>
