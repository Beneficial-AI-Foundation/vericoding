import Mathlib
-- <vc-preamble>
import Std.Data.HashSet

@[reducible, simp]
def uniqueProduct_precond (arr : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this verification condition.
-- </vc-helpers>

-- <vc-definitions>
def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  arr.toList.eraseDups.foldl (· * ·) (1 : Int)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def uniqueProduct_postcond (arr : Array Int) (result: Int) (h_precond : uniqueProduct_precond (arr)) :=
  result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0

theorem uniqueProduct_spec_satisfied (arr: Array Int) (h_precond : uniqueProduct_precond (arr)) :
    uniqueProduct_postcond (arr) (uniqueProduct (arr) h_precond) h_precond := by
  unfold uniqueProduct_postcond
  constructor <;> simp [uniqueProduct]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "arr": "#[2, 3, 2, 4]"
        },
        "expected": 24,
        "unexpected": [
            12,
            30,
            0
        ]
    },
    {
        "input": {
            "arr": "#[5, 5, 5, 5]"
        },
        "expected": 5,
        "unexpected": [
            25,
            0,
            10
        ]
    },
    {
        "input": {
            "arr": "#[]"
        },
        "expected": 1,
        "unexpected": [
            0,
            -1,
            2
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 3]"
        },
        "expected": 6,
        "unexpected": [
            5,
            7,
            2
        ]
    },
    {
        "input": {
            "arr": "#[0, 2, 3]"
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            10
        ]
    },
    {
        "input": {
            "arr": "#[-1, -2, -1, -3]"
        },
        "expected": -6,
        "unexpected": [
            -1,
            6,
            -3
        ]
    },
    {
        "input": {
            "arr": "#[10, 10, 20, 20, 30]"
        },
        "expected": 6000,
        "unexpected": [
            600,
            0,
            5000
        ]
    }
]
-/