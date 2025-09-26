import Mathlib
-- <vc-preamble>
@[reducible]
def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
@[simp]
theorem all_filter_prop {α} (p : α → Bool) (l : List α) : (l.filter p).all p := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.filter_cons, List.all_cons]
    split_ifs with heq
    · simp [heq, ih]
    · simp [ih]
-- </vc-helpers>

-- <vc-definitions>
def partitionEvensOdds (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) : (List Nat × List Nat) :=
  (nums.filter (fun n => n % 2 == 0), nums.filter (fun n => n % 2 == 1))
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def partitionEvensOdds_postcond (nums : List Nat) (result: (List Nat × List Nat)) (h_precond : partitionEvensOdds_precond (nums)): Prop :=
  let evens := result.fst
  let odds := result.snd
  -- All elements from nums are in evens ++ odds, no extras
  evens ++ odds = nums.filter (fun n => n % 2 == 0) ++ nums.filter (fun n => n % 2 == 1) ∧
  evens.all (fun n => n % 2 == 0) ∧
  odds.all (fun n => n % 2 == 1)

theorem partitionEvensOdds_spec_satisfied (nums: List Nat) (h_precond : partitionEvensOdds_precond (nums)) :
    partitionEvensOdds_postcond (nums) (partitionEvensOdds (nums) h_precond) h_precond := by
  unfold partitionEvensOdds_postcond partitionEvensOdds
  simp
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "nums": "[1, 2, 3, 4, 5, 6]"
        },
        "expected": "([2, 4, 6], [1, 3, 5])",
        "unexpected": [
            "([1, 3, 5], [2, 4, 6])"
        ]
    },
    {
        "input": {
            "nums": "[0, 7, 8, 9, 10]"
        },
        "expected": "([0, 8, 10], [7, 9])",
        "unexpected": [
            "([8, 0, 10], [9, 7])"
        ]
    },
    {
        "input": {
            "nums": "[]"
        },
        "expected": "([], [])",
        "unexpected": [
            "([0], [1])"
        ]
    },
    {
        "input": {
            "nums": "[2, 4, 6, 8]"
        },
        "expected": "([2, 4, 6, 8], [])",
        "unexpected": [
            "([], [2, 4, 6, 8])"
        ]
    },
    {
        "input": {
            "nums": "[1, 3, 5, 7]"
        },
        "expected": "([], [1, 3, 5, 7])",
        "unexpected": [
            "([1, 3, 5, 7], [])"
        ]
    }
]
-/