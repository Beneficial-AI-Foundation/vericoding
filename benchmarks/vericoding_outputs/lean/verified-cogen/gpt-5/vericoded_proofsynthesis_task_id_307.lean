import Mathlib
-- <vc-preamble>
-- <vc-preamble>
@[reducible, simp]
def listDeepClone_precond (arr : Array Nat) :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed for this task
-- </vc-helpers>

-- <vc-definitions>
def listDeepClone (arr : Array Nat) (h_precond : listDeepClone_precond (arr)) : Array Nat :=
  arr
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def listDeepClone_postcond (arr : Array Nat) (copied: Array Nat) (h_precond : listDeepClone_precond (arr)) :=
  arr.size = copied.size ∧ (∀ i, i < arr.size → arr[i]! = copied[i]!)

theorem listDeepClone_spec_satisfied (arr: Array Nat) (h_precond : listDeepClone_precond (arr)) :
    listDeepClone_postcond (arr) (listDeepClone (arr) h_precond) h_precond := by
  unfold listDeepClone_postcond listDeepClone
  constructor
  · rfl
  · intro i hi
    rfl
-- </vc-theorems>
