/- 
-----Description-----
This task requires writing a Lean 4 function that finds the length of the longest sequence of consecutive integers present in a given list. The numbers do not need to appear in order. The elements are unique.

A consecutive sequence consists of integers that can be arranged in increasing order with no gaps. Your function should find the longest such streak.

-----Input-----
- nums: A list of integers (no duplicates).

-----Output-----
- A natural number: the length of the longest consecutive sequence.
-/

import Std.Data.HashSet
import Mathlib
open Std

@[reducible, simp]
def longestConsecutive_precond (nums : List Int) : Prop :=
  List.Nodup nums

-- <vc-helpers>
-- </vc-helpers>

def longestConsecutive (nums : List Int) (h_precond : longestConsecutive_precond (nums)) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def isConsecutive (seq : List Int) : Bool :=
  seq.length = 0 ∨ seq.zipIdx.all (fun (x, i) => x = i + seq[0]!)
@[reducible, simp]
def longestConsecutive_postcond (nums : List Int) (result: Nat) (h_precond : longestConsecutive_precond (nums)) : Prop :=
  let sorted_nums := nums.mergeSort
  let consec_sublist_lens := List.range nums.length |>.flatMap (fun start =>
    List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length)

  (nums = [] → result = 0) ∧
  (nums ≠ [] → consec_sublist_lens.contains result ∧ consec_sublist_lens.all (· ≤ result))

theorem longestConsecutive_spec_satisfied (nums: List Int) (h_precond : longestConsecutive_precond (nums)) :
    longestConsecutive_postcond (nums) (longestConsecutive (nums) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[1, 1]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[100, 4, 200, 1, 3, 2]"
        },
        "expected": 4,
        "unexpected": [
            3,
            5
        ]
    },
    {
        "input": {
            "nums": "[0, 3, 7, 2, 5, 8, 4, 6, 1]"
        },
        "expected": 9,
        "unexpected": [
            8
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 0]"
        },
        "expected": 3,
        "unexpected": [
            2
        ]
    },
    {
        "input": {
            "nums": "[]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "nums": "[10]"
        },
        "expected": 1,
        "unexpected": [
            0
        ]
    }
]
-/