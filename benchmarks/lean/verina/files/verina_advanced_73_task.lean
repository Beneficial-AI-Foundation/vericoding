@[reducible]
def smallestMissing_precond (l : List Nat) : Prop :=
  List.Pairwise (· < ·) l

-- <vc-helpers>
-- </vc-helpers>

def smallestMissing (l : List Nat) (h_precond : smallestMissing_precond (l)) : Nat :=
  sorry

@[reducible]
def smallestMissing_postcond (l : List Nat) (result: Nat) (h_precond : smallestMissing_precond (l)) : Prop :=
  result ∉ l ∧ ∀ candidate : Nat, candidate < result → candidate ∈ l

theorem smallestMissing_spec_satisfied (l: List Nat) (h_precond : smallestMissing_precond (l)) :
    smallestMissing_postcond (l) (smallestMissing (l) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "l": "[1, 1]"
        }
    },
    {
        "input": {
            "l": "[1, 0]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "l": "[0, 1, 2, 4, 5]"
        },
        "expected": 3,
        "unexpected": [
            1,
            2,
            0
        ]
    },
    {
        "input": {
            "l": "[]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            3
        ]
    },
    {
        "input": {
            "l": "[1, 2, 3, 4]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            3,
            4
        ]
    },
    {
        "input": {
            "l": "[0, 1, 2, 3, 4]"
        },
        "expected": 5,
        "unexpected": [
            0,
            1,
            2,
            3,
            4
        ]
    },
    {
        "input": {
            "l": "[2, 3, 4, 5, 6]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            3,
            4,
            5,
            6
        ]
    }
]
-/