import Mathlib
-- <vc-preamble>
@[reducible, simp]
def removeKthElement_precond (list : Array Int) (k : Nat) :=
  list.size > 0 ∧ 0 < k ∧ k < list.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Simple helper for reasoning about array operations
lemma removeKth_toList_eq (list : Array Int) (k : Nat) :
  (Array.mk (list.toList.take (k - 1)) ++ Array.mk (list.toList.drop k)).toList = 
  list.toList.take (k - 1) ++ list.toList.drop k := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def removeKthElement (list : Array Int) (k : Nat) (h_precond : removeKthElement_precond list k) : Array Int :=
  Array.mk (list.toList.take (k - 1)) ++ Array.mk (list.toList.drop k)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeKthElement_postcond (list : Array Int) (k : Nat) (new_list : Array Int) (h_precond : removeKthElement_precond list k) :=
  new_list.toList = (list.toList.take (k - 1)) ++ (list.toList.drop k)

theorem removeKthElement_spec_satisfied (list : Array Int) (k : Nat) (h_precond : removeKthElement_precond list k) :
    removeKthElement_postcond list k (removeKthElement list k h_precond) h_precond := by
  unfold removeKthElement_postcond removeKthElement
  simp
-- </vc-theorems>

def main : IO Unit := pure ()