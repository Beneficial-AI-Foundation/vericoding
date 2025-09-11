-- <vc-preamble>
@[reducible, simp]
def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  List.Pairwise (· ≤ ·) arr.toList
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :=
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))

theorem findFirstOccurrence_spec_satisfied (arr: Array Int) (target: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    findFirstOccurrence_postcond (arr) (target) (findFirstOccurrence (arr) (target) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "arr": "#[3, 2, 1]",
            "target": 2
        }
    }
]
-- Tests
[
    {
        "input": {
            "arr": "#[1, 2, 2, 3, 4, 5]",
            "target": 2
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            -1
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 2, 3, 4, 5]",
            "target": 6
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
            "arr": "#[1, 2, 3, 4, 5]",
            "target": 1
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
            "arr": "#[1, 2, 3, 4, 5]",
            "target": 5
        },
        "expected": 4,
        "unexpected": [
            3,
            5,
            0
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 3, 4, 5]",
            "target": 0
        },
        "expected": -1,
        "unexpected": [
            0,
            1,
            2
        ]
    }
]
-/