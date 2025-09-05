/- 
-----Description-----
This task requires writing a Lean 4 method that returns the smallest natural number missing from a given sorted list of natural numbers. In other words, starting from 0, the method should identify the first natural number that does not appear in the list. The input list is assumed to be sorted in non-decreasing order and contains only natural numbers (including 0).

-----Input-----
The input consists of:
s: A list of natural numbers sorted in non-decreasing order.

-----Output-----
The output is a natural number:
Returns the smallest natural number that does not appear in the input list.

-----Note-----
It is assumed that the input list is sorted and contains only natural numbers.
-/

@[reducible, simp]
def smallestMissingNumber_precond (s : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) s

-- <vc-helpers>
-- </vc-helpers>

def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  sorry

@[reducible, simp]
def smallestMissingNumber_postcond (s : List Nat) (result: Nat) (h_precond : smallestMissingNumber_precond (s)) :=
  ¬ List.elem result s ∧ (∀ k : Nat, k < result → List.elem k s)

theorem smallestMissingNumber_spec_satisfied (s: List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    smallestMissingNumber_postcond (s) (smallestMissingNumber (s) h_precond) h_precond := by
  sorry

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