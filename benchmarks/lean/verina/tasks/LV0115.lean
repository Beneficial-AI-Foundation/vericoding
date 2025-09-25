-- <vc-preamble>
@[reducible, simp]
def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MoveZeroesToEnd (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :=
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)

theorem MoveZeroesToEnd_spec_satisfied (arr: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    MoveZeroesToEnd_postcond (arr) (MoveZeroesToEnd (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>