-- <vc-preamble>
@[reducible, simp]
def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def lastPosition_postcond (arr : Array Int) (elem : Int) (result: Int) (h_precond : lastPosition_precond (arr) (elem)) :=
  (result ≥ 0 →
    arr[result.toNat]! = elem ∧ (arr.toList.drop (result.toNat + 1)).all (· ≠ elem)) ∧
  (result = -1 → arr.toList.all (· ≠ elem))

theorem lastPosition_spec_satisfied (arr: Array Int) (elem: Int) (h_precond : lastPosition_precond (arr) (elem)) :
    lastPosition_postcond (arr) (elem) (lastPosition (arr) (elem) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "arr": "#[3, 2, 1]",
            "elem": 2
        }
    }
]
-- Tests
[
    {
        "input": {
            "arr": "#[1, 2, 2, 3, 4, 5]",
            "elem": 2
        },
        "expected": 2,
        "unexpected": [
            0,
            1,
            3
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 2, 3, 4, 5]",
            "elem": 6
        },
        "expected": -1,
        "unexpected": [
            0,
            1,
            2
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 2, 3, 4, 5]",
            "elem": 5
        },
        "expected": 5,
        "unexpected": [
            3,
            4,
            0
        ]
    },
    {
        "input": {
            "arr": "#[1]",
            "elem": 1
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            2
        ]
    },
    {
        "input": {
            "arr": "#[1, 1, 1, 1]",
            "elem": 1
        },
        "expected": 3,
        "unexpected": [
            0,
            1,
            2
        ]
    },
    {
        "input": {
            "arr": "#[2, 2, 3, 3, 3]",
            "elem": 3
        },
        "expected": 4,
        "unexpected": [
            2,
            3,
            5
        ]
    }
]
-/