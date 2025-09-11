-- <vc-preamble>
import Std.Data.HashMap
open Std

@[reducible]
def longestGoodSubarray_precond (nums : List Nat) (k : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestGoodSubarray (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def longestGoodSubarray_postcond (nums : List Nat) (k : Nat) (result: Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) : Prop :=
  let subArrays :=
    List.range (nums.length + 1) |>.flatMap (fun start =>
      List.range (nums.length - start + 1) |>.map (fun len =>
        nums.drop start |>.take len))
  let subArrayFreqs := subArrays.map (fun arr => arr.map (fun x => arr.count x))
  let validSubArrays := subArrayFreqs.filter (fun arr => arr.all (fun x => x ≤ k))

  (nums = [] ∧ result = 0) ∨
  (nums ≠ [] ∧
    validSubArrays.any (fun arr => arr.length = result) ∧
    validSubArrays.all (fun arr => arr.length ≤ result))

theorem longestGoodSubarray_spec_satisfied (nums: List Nat) (k: Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    longestGoodSubarray_postcond (nums) (k) (longestGoodSubarray (nums) (k) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "nums": "[1, 2, 3, 1, 2, 3, 1, 2]",
            "k": 2
        },
        "expected": 6,
        "unexpected": [
            5,
            7,
            8
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 1, 2, 1, 2, 1, 2]",
            "k": 1
        },
        "expected": 2,
        "unexpected": [
            1,
            3,
            4
        ]
    },
    {
        "input": {
            "nums": "[5, 5, 5, 5, 5, 5, 5]",
            "k": 4
        },
        "expected": 4,
        "unexpected": [
            3,
            5,
            7
        ]
    },
    {
        "input": {
            "nums": "[1]",
            "k": 1
        },
        "expected": 1,
        "unexpected": [
            0,
            2
        ]
    },
    {
        "input": {
            "nums": "[2, 2, 1, 1, 3]",
            "k": 2
        },
        "expected": 5,
        "unexpected": [
            2,
            3,
            4,
            6
        ]
    }
]
-/