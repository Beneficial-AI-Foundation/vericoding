-- <vc-preamble>
@[reducible, simp]
def smallestMissingNumber_precond (s : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) s
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def smallestMissingNumber_postcond (s : List Nat) (result: Nat) (h_precond : smallestMissingNumber_precond (s)) :=
  ¬ List.elem result s ∧ (∀ k : Nat, k < result → List.elem k s)

theorem smallestMissingNumber_spec_satisfied (s: List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    smallestMissingNumber_postcond (s) (smallestMissingNumber (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "s": "[3, 2, 1]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "s": "[0, 1, 2, 6, 9]"
        },
        "expected": 3,
        "unexpected": [
            2,
            4,
            5
        ]
    },
    {
        "input": {
            "s": "[4, 5, 10, 11]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "s": "[0, 1, 2, 3, 4, 5]"
        },
        "expected": 6,
        "unexpected": [
            5,
            7
        ]
    },
    {
        "input": {
            "s": "[]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "s": "[0, 2, 3, 4]"
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            3
        ]
    }
]
-/