import Mathlib
-- <vc-preamble>
@[reducible, simp]
def findOddNumbers_precond (arr : Array UInt32) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp]
lemma toList_filter {α : Type} (p : α → Bool) (a : Array α) : (a.filter p).toList = a.toList.filter p := by
  exact Array.toList_filter
-- </vc-helpers>

-- <vc-definitions>
def findOddNumbers (arr : Array UInt32) (h_precond : findOddNumbers_precond (arr)) : Array UInt32 :=
  arr.filter (fun x => x % 2 ≠ 0)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findOddNumbers_postcond (arr : Array UInt32) (odd_numbers: Array UInt32) (h_precond : findOddNumbers_precond (arr)) :=
  odd_numbers.toList = arr.toList.filter (fun x => x % 2 ≠ 0)

theorem findOddNumbers_spec_satisfied (arr: Array UInt32) (h_precond : findOddNumbers_precond (arr)) :
    findOddNumbers_postcond (arr) (findOddNumbers (arr) h_precond) h_precond := by
  simp [findOddNumbers, findOddNumbers_postcond, toList_filter]
-- </vc-theorems>
