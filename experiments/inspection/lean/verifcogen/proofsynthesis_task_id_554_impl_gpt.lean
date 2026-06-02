import Mathlib
-- <vc-preamble>
@[reducible, simp]
def findOddNumbers_precond (arr : Array UInt32) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
open Classical
-- LLM HELPER
@[simp] lemma array_toList_mk {α : Type _} (l : List α) : (Array.mk l).toList = l := by rfl
-- </vc-helpers>

-- <vc-definitions>
def findOddNumbers (arr : Array UInt32) (h_precond : findOddNumbers_precond (arr)) : Array UInt32 :=
  Array.mk (arr.toList.filter (fun x => x % 2 ≠ 0))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findOddNumbers_postcond (arr : Array UInt32) (odd_numbers: Array UInt32) (h_precond : findOddNumbers_precond (arr)) :=
  odd_numbers.toList = arr.toList.filter (fun x => x % 2 ≠ 0)

theorem findOddNumbers_spec_satisfied (arr: Array UInt32) (h_precond : findOddNumbers_precond (arr)) :
    findOddNumbers_postcond (arr) (findOddNumbers (arr) h_precond) h_precond := by
  simp [findOddNumbers, findOddNumbers_postcond]
-- </vc-theorems>
