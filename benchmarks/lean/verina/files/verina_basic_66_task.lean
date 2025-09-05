/- 
-----Description-----
This task focuses on determining if a given integer is even. The problem requires checking whether the integer can be represented as twice another integer, meaning it is divisible by 2 without any remainder.

-----Input-----
The input consists of a single integer:
• x: An integer to be evaluated.

-----Output-----
The output is a boolean value:
• true if x is even (x mod 2 equals 0).
• false if x is odd.

-----Note-----
No additional preconditions are required. The method should work correctly for any integer value.
-/

import Mathlib

@[reducible, simp]
def ComputeIsEven_precond (x : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  result = true ↔ ∃ k : Int, x = 2 * k

theorem ComputeIsEven_spec_satisfied (x: Int) (h_precond : ComputeIsEven_precond (x)) :
    ComputeIsEven_postcond (x) (ComputeIsEven (x) h_precond) h_precond := by
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
            "x": 4
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": 7
        },
        "expected": false,
        "unexpected": [true]
    },
    {
        "input": {
            "x": 0
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": -2
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": -3
        },
        "expected": false,
        "unexpected": [true]
    }
]
-/
