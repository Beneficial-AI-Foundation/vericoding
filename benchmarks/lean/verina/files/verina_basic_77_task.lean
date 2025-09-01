/- 
-----Description-----
This task involves updating an element within a 2-dimensional array. The goal is to modify only a specific inner array by changing one of its elements to a new value while keeping every other element and all other inner arrays unchanged.

-----Input-----
The input consists of:
• arr: An array of arrays of natural numbers.
• index1: A natural number representing the index in the outer array identifying which inner array to modify (0-indexed).
• index2: A natural number representing the index within the selected inner array that should be updated (0-indexed).
• val: A natural number which is the new value to set at the specified inner index.

-----Output-----
The output is an array of arrays of natural numbers that:
• Has the same overall structure as the input.
• Contains all original inner arrays unchanged except for the inner array at position index1.
• In the modified inner array, only the element at index2 is replaced with val, while all other elements remain the same.

-----Note-----
It is assumed that index1 is a valid index for the outer array and that index2 is a valid index within the corresponding inner array.
-/

@[reducible, simp]
def modify_array_element_precond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧
  index2 < (arr[index1]!).size

-- <vc-helpers>
def updateInner (a : Array Nat) (idx val : Nat) : Array Nat :=
  a.set! idx val
-- </vc-helpers>

def modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) : Array (Array Nat) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def modify_array_element_postcond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result: Array (Array Nat)) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :=
  (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
  (∀ j, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
  ((result[index1]!)[index2]! = val)

theorem modify_array_element_spec_satisfied (arr: Array (Array Nat)) (index1: Nat) (index2: Nat) (val: Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :
    modify_array_element_postcond (arr) (index1) (index2) (val) (modify_array_element (arr) (index1) (index2) (val) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[
    {
        "input": {
            "arr": "#[#[1, 2, 3], #[4, 5, 6]]",
            "index1": 1,
            "index2": 3,
            "val": 99
        }
    }
]
-- Tests
[
    {
        "input": {
            "arr": "#[#[1, 2, 3], #[4, 5, 6]]",
            "index1": 0,
            "index2": 1,
            "val": 99
        },
        "expected": "#[#[1, 99, 3], #[4, 5, 6]]",
        "unexpected": [
            "#[#[1, 2, 3], #[4, 99, 6]]",
            "#[#[1, 99, 3], #[4, 5, 7]]",
            "#[#[99, 1, 3], #[4, 5, 6]]"
        ]
    },
    {
        "input": {
            "arr": "#[#[7, 8], #[9, 10]]",
            "index1": 1,
            "index2": 0,
            "val": 0
        },
        "expected": "#[#[7, 8], #[0, 10]]",
        "unexpected": [
            "#[#[7, 0], #[9, 10]]",
            "#[#[7, 8], #[9, 0]]",
            "#[#[0, 8], #[9, 10]]"
        ]
    },
    {
        "input": {
            "arr": "#[#[0, 0, 0]]",
            "index1": 0,
            "index2": 2,
            "val": 5
        },
        "expected": "#[#[0, 0, 5]]",
        "unexpected": [
            "#[#[0, 5, 0]]",
            "#[#[5, 0, 0]]"
        ]
    },
    {
        "input": {
            "arr": "#[#[3, 4, 5], #[6, 7, 8], #[9, 10, 11]]",
            "index1": 2,
            "index2": 1,
            "val": 100
        },
        "expected": "#[#[3, 4, 5], #[6, 7, 8], #[9, 100, 11]]",
        "unexpected": [
            "#[#[3, 4, 5], #[6, 7, 8], #[9, 10, 11]]",
            "#[#[3, 4, 5], #[6, 7, 8], #[9, 7, 11]]",
            "#[#[3, 4, 5], #[6, 7, 8], #[100, 10, 11]]"
        ]
    },
    {
        "input": {
            "arr": "#[#[1]]",
            "index1": 0,
            "index2": 0,
            "val": 42
        },
        "expected": "#[#[42]]",
        "unexpected": [
            "#[#[1]]",
            "#[#[0]]",
            "#[#[99]]"
        ]
    }
]
-/