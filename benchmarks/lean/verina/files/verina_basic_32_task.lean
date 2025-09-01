/- 
-----Description-----
This task requires writing a Lean 4 method that swaps the first and last elements of an array of integers. The method should produce a new array where the first element of the output is the last element of the input, the last element of the output is the first element of the input, and all other elements remain in their original positions.

-----Input-----
The input consists of:
a: An array of integers (assumed to be non-empty).

-----Output-----
The output is an array of integers:
Returns a new array where:
- The former last element becomes the first element.
- The former first element becomes the last element.
- All other elements remain unchanged.
-/

import Mathlib

def swapFirstAndLast_precond (a : Array Int) : Prop :=
  a.size > 0

-- <vc-helpers>
-- </vc-helpers>

def swapFirstAndLast (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

-- Theorem: The last element of the input array should be the first element of the modified array; The first element of the input array should be the last element of the modified array; All other elements remain unchanged
@[reducible, simp]
def swapFirstAndLast_postcond (a : Array Int) (result : Array Int) (h_precond: swapFirstAndLast_precond a) : Prop :=
  result.size = a.size ∧
  result[0]! = a[a.size - 1]! ∧
  result[result.size - 1]! = a[0]! ∧
  (List.range (result.size - 2)).all (fun i => result[i + 1]! = a[i + 1]!)

theorem swapFirstAndLast_spec_satisfied (a : Array Int) (h_precond: swapFirstAndLast_precond a) :
    swapFirstAndLast_postcond a (swapFirstAndLast a h_precond) h_precond := by
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
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": "#[5, 2, 3, 4, 1]",
        "unexpected": [
            "#[1, 2, 3, 4, 5]",
            "#[5, 4, 3, 2, 1]",
            "#[2, 3, 4, 5, 1]"
        ]
    },
    {
        "input": {
            "a": "#[10]"
        },
        "expected": "#[10]",
        "unexpected": [
            "#[0]",
            "#[5]",
            "#[11]"
        ]
    },
    {
        "input": {
            "a": "#[1, 2]"
        },
        "expected": "#[2, 1]",
        "unexpected": [
            "#[1, 2]",
            "#[2, 2]",
            "#[1, 1]"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3]"
        },
        "expected": "#[3, 2, 1]",
        "unexpected": [
            "#[1, 2, 3]",
            "#[3, 1, 2]",
            "#[2, 1, 3]"
        ]
    }
]
-/