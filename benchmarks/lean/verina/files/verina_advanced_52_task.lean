/- 
-----Description-----
This task requires writing a Lean 4 function that finds the minimum number of operations to collect the integers from 1 to k by performing the following removal operation on a list of integers.

A removal operation consists of removing the last element from the list nums and adding it to your collection.

The goal is to determine how many elements must be removed from the end of the list until the set of collected elements (that are less than or equal to k) contains all integers from 1 to k, inclusive.

-----Input-----
The input consists of a list and a positive integer:
nums: A list of positive integers.
k: A positive integer representing the target upper bound for the collection (i.e., we want to collect 1, 2, ..., k).

-----Output-----
The output is an integer:
Return the minimum number of operations (elements removed from the end of nums) required to have collected all integers from 1 to k.

-----Note-----
It is assumed that the input list contains all integers from 1 to k.
-/

@[reducible, simp]
def minOperations_precond (nums : List Nat) (k : Nat) : Prop :=
  let target_nums := (List.range k).map (· + 1)
  target_nums.all (fun n => List.elem n nums)

-- <vc-helpers>
-- </vc-helpers>

def minOperations (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) : Nat :=
  sorry

@[reducible, simp]
def minOperations_postcond (nums : List Nat) (k : Nat) (result: Nat) (h_precond : minOperations_precond (nums) (k)) : Prop :=
  -- define the list of elements processed after `result` operations
  let processed := (nums.reverse).take result
  -- define the target numbers to collect (1 to k)
  let target_nums := (List.range k).map (· + 1)

  -- condition 1: All target numbers must be present in the processed elements
  let collected_all := target_nums.all (fun n => List.elem n processed)

  -- condition 2: `result` must be the minimum number of operations.
  -- This means either result is 0 (which implies k must be 0 as target_nums would be empty)
  -- or result > 0, and taking one less operation (result - 1) is not sufficient
  let is_minimal :=
    if result > 0 then
      -- if one fewer element is taken, not all target numbers should be present
      let processed_minus_one := (nums.reverse).take (result - 1)
      ¬ (target_nums.all (fun n => List.elem n processed_minus_one))
    else
      -- if result is 0, it can only be minimal if k is 0 (no targets required)
      -- So if k=0, `collected_all` is true. If result=0, this condition `k==0` ensures minimality.
      k == 0

  -- overall specification:
  collected_all ∧ is_minimal

theorem minOperations_spec_satisfied (nums: List Nat) (k: Nat) (h_precond : minOperations_precond (nums) (k)) :
    minOperations_postcond (nums) (k) (minOperations (nums) (k) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[5, 6, 7, 8, 9]",
            "k": 3
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[3, 1, 5, 4, 2]",
            "k": 2
        },
        "expected": 4,
        "unexpected": [
            1,
            2,
            5
        ]
    },
    {
        "input": {
            "nums": "[3, 1, 5, 4, 2]",
            "k": 5
        },
        "expected": 5,
        "unexpected": [
            1,
            2,
            3
        ]
    },
    {
        "input": {
            "nums": "[3, 2, 5, 3, 1]",
            "k": 3
        },
        "expected": 4,
        "unexpected": [
            1,
            2,
            5
        ]
    },
    {
        "input": {
            "nums": "[5, 4, 3, 2, 1]",
            "k": 1
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            5
        ]
    },
    {
        "input": {
            "nums": "[5, 4, 1, 2, 3]",
            "k": 3
        },
        "expected": 3,
        "unexpected": [
            1,
            4,
            5
        ]
    },
    {
        "input": {
            "nums": "[1, 3, 2, 2, 1]",
            "k": 2
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
            "nums": "[10, 1, 20, 2]",
            "k": 2
        },
        "expected": 3,
        "unexpected": [
            1,
            2,
            4
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 3]",
            "k": 0
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            3
        ]
    }
]
-/