/- 
-----Description-----
This task requires writing a Lean 4 method that searches an array of integers to locate the first odd number. The method should return a pair where the first element is a Boolean indicating whether an odd number was found, and the second element is the index of that odd number if found, or -1 if no odd number exists. When an odd number is found, the method should return the smallest index at which an odd number occurs.

-----Input-----
The input consists of:
a: An array of integers.

-----Output-----
The output is a pair (Bool, Int):
- If the Boolean is true, then the integer represents the smallest index of an odd number in the array.
- If the Boolean is false, then there are no odd numbers in the array, and the accompanying integer is -1.

-----Note-----
- The input array is assumed to be non-null.
- If multiple odd numbers are present, the index returned should correspond to the first occurrence.
-/

@[reducible, simp]
def findFirstOdd_precond (a : Array Int) : Prop :=
  a.size > 0

-- <vc-helpers>
def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0
-- </vc-helpers>

def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)

theorem findFirstOdd_spec_satisfied (a: Array Int) (h_precond : findFirstOdd_precond (a)) :
    findFirstOdd_postcond (a) (findFirstOdd (a) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[2, 4, 6, 8]"
        },
        "expected": "none",
        "unexpected": [
            "some (0)"
        ]
    },
    {
        "input": {
            "a": "#[3, 4, 6, 8]"
        },
        "expected": "some (0)",
        "unexpected": [
            "some (1)",
            "some (2)",
            "none"
        ]
    },
    {
        "input": {
            "a": "#[2, 4, 5, 8]"
        },
        "expected": "some (2)",
        "unexpected": [
            "some (0)",
            "some (1)",
            "some (3)",
            "none"
        ]
    },
    {
        "input": {
            "a": "#[7]"
        },
        "expected": "some (0)",
        "unexpected": [
            "some (1)",
            "none"
        ]
    },
    {
        "input": {
            "a": "#[2]"
        },
        "expected": "none",
        "unexpected": [
            "some (0)"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3]"
        },
        "expected": "some (0)",
        "unexpected": [
            "some (1)",
            "some (2)",
            "none"
        ]
    }
]
-/