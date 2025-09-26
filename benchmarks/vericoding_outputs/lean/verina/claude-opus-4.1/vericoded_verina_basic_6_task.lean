-- <vc-preamble>
import Mathlib

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  if a <= b && a <= c then a
  else if b <= c then b
  else c
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)

theorem minOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
  unfold minOfThree_postcond minOfThree
  split_ifs with h1 h2
  · -- case: a <= b && a <= c
    -- LLM HELPER
    have hab : a ≤ b := by
      simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1.1
    -- LLM HELPER  
    have hac : a ≤ c := by
      simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1.2
    constructor
    · exact And.intro (le_refl a) (And.intro hab hac)
    · left; rfl
  · -- case: ¬(a <= b && a <= c) but b <= c
    constructor
    · -- LLM HELPER
      have not_both : ¬(a ≤ b ∧ a ≤ c) := by
        intro h
        simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h1
        exact h1 (And.intro h.1 h.2)
      -- LLM HELPER
      have hbc : b ≤ c := h2
      -- LLM HELPER
      have hba : b ≤ a := by
        by_contra h
        push_neg at h
        have : a ≤ b := le_of_lt h
        have hac : a ≤ c := le_trans this hbc
        exact not_both (And.intro this hac)
      exact And.intro hba (And.intro (le_refl b) hbc)
    · right; left; rfl
  · -- case: ¬(a <= b && a <= c) and ¬(b <= c)
    constructor
    · -- LLM HELPER
      have not_both : ¬(a ≤ b ∧ a ≤ c) := by
        intro h
        simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h1
        exact h1 (And.intro h.1 h.2)
      -- LLM HELPER
      have hcb : c ≤ b := by
        by_contra h
        push_neg at h
        have : b ≤ c := le_of_lt h
        exact h2 this
      -- LLM HELPER
      have hca : c ≤ a := by
        by_contra h
        push_neg at h
        have : a ≤ c := le_of_lt h
        have hab : a ≤ b := le_trans this hcb
        exact not_both (And.intro hab this)
      exact And.intro hca (And.intro hcb (le_refl c))
    · right; right; rfl
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