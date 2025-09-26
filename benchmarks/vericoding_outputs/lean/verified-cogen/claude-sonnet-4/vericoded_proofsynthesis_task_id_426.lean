import Mathlib
-- <vc-preamble>
@[reducible, simp]
def filterOddNumbers_precond (arr : Array UInt32) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def UInt32.isOdd (x : UInt32) : Bool := x % 2 != 0

-- LLM HELPER  
lemma UInt32.isOdd_eq (x : UInt32) : UInt32.isOdd x = (x % 2 != 0) := rfl
-- </vc-helpers>

-- <vc-definitions>
def filterOddNumbers (arr : Array UInt32) (h_precond : filterOddNumbers_precond (arr)) : Array UInt32 :=
  arr.filter UInt32.isOdd
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def filterOddNumbers_postcond (arr : Array UInt32) (odd_list: Array UInt32) (h_precond : filterOddNumbers_precond (arr)) :=
  odd_list.toList = arr.toList.filter (fun x => x % 2 ≠ 0)

theorem filterOddNumbers_spec_satisfied (arr: Array UInt32) (h_precond : filterOddNumbers_precond (arr)) :
    filterOddNumbers_postcond (arr) (filterOddNumbers (arr) h_precond) h_precond := by
  unfold filterOddNumbers_postcond filterOddNumbers
  rw [Array.toList_filter]
  congr
  ext x
  simp [UInt32.isOdd]
  rfl
-- </vc-theorems>

def main : IO Unit := pure ()