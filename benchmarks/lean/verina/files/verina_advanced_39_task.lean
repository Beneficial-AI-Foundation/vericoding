/- 
-----Description-----
This task requires writing a Lean 4 function that returns the maximum element from a non-empty list of natural numbers.

-----Input-----
The input consists of:
lst: a non-empty list of natural numbers.

-----Output-----
The output is:
A natural number representing the largest element in the list.
-/

@[reducible, simp]
def maxOfList_precond (lst : List Nat) : Prop :=
  lst.length > 0

-- <vc-helpers>
-- </vc-helpers>

def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result

theorem maxOfList_spec_satisfied (lst: List Nat) (h_precond : maxOfList_precond (lst)) :
    maxOfList_postcond (lst) (maxOfList (lst) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[
    {
        "input": {
            "lst": "[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "lst": "[1, 2, 3]"
        },
        "expected": 3,
        "unexpected": [
            2,
            1,
            0
        ]
    },
    {
        "input": {
            "lst": "[5, 5, 5]"
        },
        "expected": 5,
        "unexpected": [
            4,
            0
        ]
    },
    {
        "input": {
            "lst": "[10, 1, 9]"
        },
        "expected": 10,
        "unexpected": [
            1,
            9
        ]
    },
    {
        "input": {
            "lst": "[7]"
        },
        "expected": 7,
        "unexpected": [
            0,
            6
        ]
    },
    {
        "input": {
            "lst": "[0, 0, 0, 0]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    }
]
-/