import Mathlib
-- <vc-preamble>
@[reducible, simp]
def splitArray_precond (list : Array Int) (l : Nat) : Prop :=
  list.size > 0 ∧ 0 < l ∧ l < list.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem list_toArray_toList {α : Type _} (xs : List α) : xs.toArray.toList = xs := by
  simp [List.toArray_toList]
-- </vc-helpers>

-- <vc-definitions>
def splitArray (list : Array Int) (l : Nat) (h_precond : splitArray_precond list l) : Array Int × Array Int :=
  let xs := list.toList
let left := (xs.take l).toArray
let right := (xs.drop l).toArray
(left, right)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def splitArray_postcond (list : Array Int) (l : Nat) (result: Array Int × Array Int) (h_precond : splitArray_precond list l) : Prop :=
  result.1.toList = list.toList.take l ∧ result.2.toList = list.toList.drop l

theorem splitArray_spec_satisfied (list: Array Int) (l: Nat) (h_precond : splitArray_precond list l) :
    splitArray_postcond list l (splitArray list l h_precond) h_precond := by
  simp [splitArray, splitArray_postcond, list_toArray_toList]
-- </vc-theorems>
