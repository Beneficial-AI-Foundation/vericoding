-- <vc-preamble>
@[reducible, simp]
def filterOddNumbers_precond (arr : Array UInt32) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def filterOddNumbers (arr : Array UInt32) (h_precond : filterOddNumbers_precond (arr)) : Array UInt32 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def filterOddNumbers_postcond (arr : Array UInt32) (odd_list: Array UInt32) (h_precond : filterOddNumbers_precond (arr)) :=
  odd_list.toList = arr.toList.filter (fun x => x % 2 ≠ 0)

theorem filterOddNumbers_spec_satisfied (arr: Array UInt32) (h_precond : filterOddNumbers_precond (arr)) :
    filterOddNumbers_postcond (arr) (filterOddNumbers (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>