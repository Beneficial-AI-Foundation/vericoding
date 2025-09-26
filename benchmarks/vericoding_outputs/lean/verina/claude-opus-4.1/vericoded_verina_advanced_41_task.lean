import Mathlib
-- <vc-preamble>
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if a >= b && a >= c then a else if b >= c then b else c
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)

theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
  unfold maxOfThree_postcond maxOfThree
  split_ifs with h1 h2
  · -- case: a >= b && a >= c
    have hab : a ≥ b := by
      have : decide (a ≥ b) = true ∧ decide (a ≥ c) = true := by
        simpa using h1
      exact decide_eq_true_iff.mp this.1
    have hac : a ≥ c := by
      have : decide (a ≥ b) = true ∧ decide (a ≥ c) = true := by
        simpa using h1
      exact decide_eq_true_iff.mp this.2
    constructor
    · exact ⟨le_refl a, hab, hac⟩
    · left; rfl
  · -- case: ¬(a >= b && a >= c) but b >= c
    constructor
    · constructor
      · -- b ≥ a
        by_contra hba
        push_neg at hba
        have : a ≥ b ∧ a ≥ c := ⟨le_of_lt hba, le_trans h2 (le_of_lt hba)⟩
        have : (decide (a ≥ b) && decide (a ≥ c)) = true := by
          simp [this.1, this.2]
        exact h1 this
      · exact ⟨le_refl b, h2⟩
    · right; left; rfl
  · -- case: ¬(a >= b && a >= c) and ¬(b >= c)
    push_neg at h2
    constructor
    · constructor
      · -- c ≥ a
        by_contra hca
        push_neg at hca
        have hac : a > c := hca
        have hbc : b < c := h2
        have hab : a > b := lt_trans hbc hac
        have : (decide (a ≥ b) && decide (a ≥ c)) = true := by
          simp [le_of_lt hab, le_of_lt hac]
        exact h1 this
      · constructor
        · -- c ≥ b
          exact le_of_lt h2
        · -- c ≥ c
          exact le_refl c
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
        "expected": 3,
        "unexpected": [
            2,
            1,
            -1
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
            6,
            4
        ]
    },
    {
        "input": {
            "a": 10,
            "b": 20,
            "c": 15
        },
        "expected": 20,
        "unexpected": [
            10,
            15
        ]
    },
    {
        "input": {
            "a": -1,
            "b": -2,
            "c": -3
        },
        "expected": -1,
        "unexpected": [
            -2,
            -3
        ]
    },
    {
        "input": {
            "a": 0,
            "b": -10,
            "c": -5
        },
        "expected": 0,
        "unexpected": [
            -5,
            -10
        ]
    }
]
-/