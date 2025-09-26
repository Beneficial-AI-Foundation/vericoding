-- <vc-preamble>
import Mathlib

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma min_eq_left_or_eq_right {α : Type*} [LinearOrder α] (a b : α) : min a b = a ∨ min a b = b :=
  min_choice a b
-- </vc-helpers>

-- <vc-definitions>
def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  min a (min b c)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)

theorem minOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
  unfold minOfThree minOfThree_postcond
  constructor
  · refine' ⟨min_le_left _ _, _, _⟩
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  · rcases min_eq_left_or_eq_right a (min b c) with h | h
    · left
      exact h
    · rcases min_eq_left_or_eq_right b c with h' | h'
      · right; left
        exact h.trans h'
      · right; right
        exact h.trans h'
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": 3,
            "b": 2,
            "c": 1
        },
        "expected": 1,
        "unexpected": [
            2,
            3,
            0
        ]
    },
    {
        "input": {
            "a": 5,
            "b": 5,
            "c": 5
        },
        "expected": 5,
        "unexpected": [
            4,
            6
        ]
    },
    {
        "input": {
            "a": 10,
            "b": 20,
            "c": 15
        },
        "expected": 10,
        "unexpected": [
            15,
            20,
            5
        ]
    },
    {
        "input": {
            "a": -1,
            "b": 2,
            "c": 3
        },
        "expected": -1,
        "unexpected": [
            2,
            3,
            0
        ]
    },
    {
        "input": {
            "a": 2,
            "b": -3,
            "c": 4
        },
        "expected": -3,
        "unexpected": [
            2,
            4,
            0
        ]
    },
    {
        "input": {
            "a": 2,
            "b": 3,
            "c": -5
        },
        "expected": -5,
        "unexpected": [
            2,
            3,
            0
        ]
    },
    {
        "input": {
            "a": 0,
            "b": 0,
            "c": 1
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            2
        ]
    },
    {
        "input": {
            "a": 0,
            "b": -1,
            "c": 1
        },
        "expected": -1,
        "unexpected": [
            0,
            1,
            2
        ]
    },
    {
        "input": {
            "a": -5,
            "b": -2,
            "c": -3
        },
        "expected": -5,
        "unexpected": [
            -2,
            -3,
            0
        ]
    }
]
-/