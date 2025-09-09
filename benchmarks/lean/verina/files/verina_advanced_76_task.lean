/- 
-----Description-----
This task requires writing a Lean 4 method that returns the k most frequent elements from a list of integers. The method should count the frequency of each distinct element in the list and return the k elements with the highest frequency.

-----Input-----
The input consists of two values:
nums: A list of integers, possibly with duplicates.
k: A natural number indicating how many of the most frequent elements to return. Assimng k <= # of distinct elements in nums.

-----Output-----
The output is a list of integers:
Returns exactly k integers representing the elements that appear most frequently in the input list in the order form the higher frequency to lower frequency.
If two numbers have the same frequency, use the order of the first occurance in nums.
-/

import Std
open Std

@[reducible]
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  k ≤ nums.eraseDups.length

-- <vc-helpers>
-- </vc-helpers>

def topKFrequent (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) : List Int :=
  sorry

@[reducible]
def topKFrequent_postcond (nums : List Int) (k : Nat) (result: List Int) (h_precond : topKFrequent_precond (nums) (k)) : Prop :=
  -- Result contains exactly k elements
  result.length = k ∧

  -- All elements in result appear in the original list
  result.all (· ∈ nums) ∧

  -- All elements in result are distinct
  List.Pairwise (· ≠ ·) result ∧

  -- For any element in result and any element not in result, the frequency of the
  -- element in result is greater or equal
  (result.all (fun x =>
    nums.all (fun y =>
      y ∉ result →
        nums.count x > nums.count y ∨
        (nums.count x == nums.count y ∧ nums.idxOf x < nums.idxOf y)
    ))) ∧

  -- Elements in result are ordered by decreasing frequency
  List.Pairwise (fun (x, i) (y, j) =>
    i < j → nums.count x > nums.count y ∨
    (nums.count x == nums.count y ∧ nums.idxOf x < nums.idxOf y)
  ) result.zipIdx

theorem topKFrequent_spec_satisfied (nums: List Int) (k: Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    topKFrequent_postcond (nums) (k) (topKFrequent (nums) (k) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[1, 2, 3]",
            "k": 4
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[1, 1, 1, 2, 2, 3]",
            "k": 2
        },
        "expected": "[1, 2]",
        "unexpected": [
            "[1, 3]",
            "[2, 3]"
        ]
    },
    {
        "input": {
            "nums": "[4, 1, -1, 2, -1, 2, 3]",
            "k": 2
        },
        "expected": "[-1, 2]",
        "unexpected": [
            "[-1, 4]",
            "[4, 3]"
        ]
    },
    {
        "input": {
            "nums": "[5]",
            "k": 1
        },
        "expected": "[5]",
        "unexpected": [
            "[]"
        ]
    },
    {
        "input": {
            "nums": "[7, 7, 7, 8, 8, 9]",
            "k": 1
        },
        "expected": "[7]",
        "unexpected": [
            "[8]"
        ]
    },
    {
        "input": {
            "nums": "[]",
            "k": 0
        },
        "expected": "[]",
        "unexpected": [
            "[0]"
        ]
    }
]
-/