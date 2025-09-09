/- 
------Description-----
This task requires writing a Lean 4 method that given a 0-indexed integer array `nums` representing the scores of students in an exam. A teacher wants to select a non empty group of students such that the strength of group is maximized.

The strength of a group is defined as the product of the selected student scores.

You can choose any non-empty subset of students. The goal is to compute the maximum product of any such subset.

----Input---
nums: An non-empty list of integers.

-----Output-----

An integer representing the maximum strength.
-/

import Mathlib

@[reducible]
def maxStrength_precond (nums : List Int) : Prop :=
  nums ≠ []

-- <vc-helpers>
-- </vc-helpers>

def maxStrength (nums : List Int) (h_precond : maxStrength_precond (nums)) : Int :=
  sorry

@[reducible]
def maxStrength_postcond (nums : List Int) (result: Int) (h_precond : maxStrength_precond (nums)) : Prop :=
  let sublists := nums.sublists.filter (· ≠ [])
  let products := sublists.map (List.foldl (· * ·) 1)
  products.contains result ∧ products.all (· ≤ result)

theorem maxStrength_spec_satisfied (nums: List Int) (h_precond : maxStrength_precond (nums)) :
    maxStrength_postcond (nums) (maxStrength (nums) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[-2]"
        },
        "expected": -2,
        "unexpected": [
            2,
            0
        ]
    },
    {
        "input": {
            "nums": "[3, -1, -5, 2, 5, -9]"
        },
        "expected": 1350,
        "unexpected": [
            270,
            0,
            -1
        ]
    },
    {
        "input": {
            "nums": "[-4, -5, -4]"
        },
        "expected": 20,
        "unexpected": [
            80,
            -80,
            -5
        ]
    },
    {
        "input": {
            "nums": "[0, -3, 4]"
        },
        "expected": 4,
        "unexpected": [
            0,
            -12
        ]
    },
    {
        "input": {
            "nums": "[1, -1, -1]"
        },
        "expected": 1,
        "unexpected": [
            -1,
            -2
        ]
    }
]
-/