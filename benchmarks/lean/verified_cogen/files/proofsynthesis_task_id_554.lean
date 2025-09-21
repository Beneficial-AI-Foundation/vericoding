-- <vc-preamble>
@[reducible, simp]
def findOddNumbers_precond (arr : Array UInt32) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findOddNumbers (arr : Array UInt32) (h_precond : findOddNumbers_precond (arr)) : Array UInt32 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findOddNumbers_postcond (arr : Array UInt32) (odd_numbers: Array UInt32) (h_precond : findOddNumbers_precond (arr)) :=
  odd_numbers.toList = arr.toList.filter (fun x => x % 2 ≠ 0)

theorem findOddNumbers_spec_satisfied (arr: Array UInt32) (h_precond : findOddNumbers_precond (arr)) :
    findOddNumbers_postcond (arr) (findOddNumbers (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>