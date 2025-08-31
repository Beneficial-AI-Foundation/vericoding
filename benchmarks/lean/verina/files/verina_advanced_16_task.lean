/- 
-----Description-----
Implement the insertion sort algorithm in Lean 4. The function takes a single list of integers
as input and returns a new list that contains the same integers in ascending order.

Implementation must follow a standard insertion sort approach, placing each element into its correct position.
The resulting list must be sorted in ascending order.
The returned list must be a permutation of the input list (i.e., contain exactly the same elements).

-----Input-----
A single list of integers, denoted as xs.

-----Output-----
A list of integers, sorted in ascending order.

Example:
Input:  [3, 1, 4, 2]
Output: [1, 2, 3, 4]
-/

@[reducible]
def insertionSort_precond (xs : List Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible]
def insertionSort_postcond (xs : List Int) (result: List Int) (h_precond : insertionSort_precond (xs)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result

theorem insertionSort_spec_satisfied (xs: List Int) (h_precond : insertionSort_precond (xs)) :
    insertionSort_postcond (xs) (insertionSort (xs) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "xs": "[]"
        },
        "expected": "[]",
        "unexpected": [
            "[0]",
            "[1, 2, 3]"
        ]
    },
    {
        "input": {
            "xs": "[42]"
        },
        "expected": "[42]",
        "unexpected": [
            "[24]",
            "[]",
            "[42, 42]"
        ]
    },
    {
        "input": {
            "xs": "[3, 1, 4, 2]"
        },
        "expected": "[1, 2, 3, 4]",
        "unexpected": [
            "[1, 3, 2, 4]",
            "[4, 3, 2, 1]"
        ]
    },
    {
        "input": {
            "xs": "[5, -1, 0, 10, -1]"
        },
        "expected": "[-1, -1, 0, 5, 10]",
        "unexpected": [
            "[-1, -1, 0, 10, 5]",
            "[10, 5, 0, -1, -1]"
        ]
    },
    {
        "input": {
            "xs": "[2, 2, 2, 2, 2]"
        },
        "expected": "[2, 2, 2, 2, 2]",
        "unexpected": [
            "[2, 2, 2, 2]",
            "[]"
        ]
    }
]
-/