/- 
-----Description-----
This task requires writing a Lean 4 method that finds the kth element in a given array using 1-based indexing. The method should return the element at the specified position, where the first element is at position 1.

-----Input-----
The input consists of:
arr: An array of integers.
k: An integer representing the position (1-based index) of the element to find.

-----Output-----
The output is an integer:
Returns the element at the kth position in the array.

-----Note-----
The input k is assumed to be valid (between 1 and array length inclusive).
The array is assumed to be non-empty.
-/

@[reducible, simp]
def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  k ≥ 1 ∧ k ≤ arr.size

-- <vc-helpers>
-- </vc-helpers>

def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  sorry

@[reducible, simp]
def kthElement_postcond (arr : Array Int) (k : Nat) (result: Int) (h_precond : kthElement_precond (arr) (k)) :=
  arr.any (fun x => x = result ∧ x = arr[k - 1]!)

theorem kthElement_spec_satisfied (arr: Array Int) (k: Nat) (h_precond : kthElement_precond (arr) (k)) :
    kthElement_postcond (arr) (k) (kthElement (arr) (k) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "arr": "#[1, 2, 3]",
            "k": 0
        }
    }
]
-- Tests
[
    {
        "input": {
            "arr": "#[10, 20, 30, 40, 50]",
            "k": 1
        },
        "expected": 10,
        "unexpected": [
            20,
            30
        ]
    },
    {
        "input": {
            "arr": "#[10, 20, 30, 40, 50]",
            "k": 3
        },
        "expected": 30,
        "unexpected": [
            10,
            40,
            50
        ]
    },
    {
        "input": {
            "arr": "#[10, 20, 30, 40, 50]",
            "k": 5
        },
        "expected": 50,
        "unexpected": [
            10,
            40
        ]
    },
    {
        "input": {
            "arr": "#[5]",
            "k": 1
        },
        "expected": 5,
        "unexpected": [
            0,
            1
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 3]",
            "k": 3
        },
        "expected": 3,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 3]",
            "k": 2
        },
        "expected": 2,
        "unexpected": [
            1,
            3,
            0
        ]
    },
    {
        "input": {
            "arr": "#[9, 9, 9]",
            "k": 2
        },
        "expected": 9,
        "unexpected": [
            0,
            7
        ]
    },
    {
        "input": {
            "arr": "#[0, -1, -2]",
            "k": 1
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
            "arr": "#[0, -1, -2]",
            "k": 2
        },
        "expected": -1,
        "unexpected": [
            0,
            -2
        ]
    },
    {
        "input": {
            "arr": "#[0, -1, -2]",
            "k": 3
        },
        "expected": -2,
        "unexpected": [
            0,
            -1
        ]
    }
]
-/