-- <vc-preamble>
import Std
open Std

@[reducible]
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  k ≤ nums.eraseDups.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def topKFrequent (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

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