@[reducible, simp]
def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def MoveZeroesToEnd (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  sorry

@[reducible, simp]
def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :=
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)

theorem MoveZeroesToEnd_spec_satisfied (arr: Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    MoveZeroesToEnd_postcond (arr) (MoveZeroesToEnd (arr) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "arr": "#[0, 1, 0, 3, 12]"
        },
        "expected": "#[1, 3, 12, 0, 0]",
        "unexpected": [
            "#[0, 1, 0, 3, 12]",
            "#[1, 0, 3, 12, 0]"
        ]
    },
    {
        "input": {
            "arr": "#[0, 0, 1]"
        },
        "expected": "#[1, 0, 0]",
        "unexpected": [
            "#[0, 0, 1]",
            "#[0, 1, 0]"
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 3]"
        },
        "expected": "#[1, 2, 3]",
        "unexpected": [
            "#[1, 3, 2]",
            "#[2, 1, 3]"
        ]
    },
    {
        "input": {
            "arr": "#[0, 0, 0]"
        },
        "expected": "#[0, 0, 0]",
        "unexpected": [
            "#[1, 0, 0]",
            "#[0, 1, 0]"
        ]
    },
    {
        "input": {
            "arr": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[0]",
            "#[1]"
        ]
    }
]
-/