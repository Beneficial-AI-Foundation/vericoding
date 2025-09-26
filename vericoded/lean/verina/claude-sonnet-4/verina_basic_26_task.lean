import Mathlib
-- <vc-preamble>
@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper lemma for modulo properties
lemma int_mod_two_eq_zero_or_one (n : Int) : n % 2 = 0 ∨ n % 2 = 1 := by
  have h := Int.emod_two_eq_zero_or_one n
  exact h

lemma int_mod_two_ne_zero_iff_eq_one (n : Int) : n % 2 ≠ 0 ↔ n % 2 = 1 := by
  constructor
  · intro h
    cases' int_mod_two_eq_zero_or_one n with h1 h2
    · contradiction
    · exact h2
  · intro h
    rw [h]
    norm_num
-- </vc-helpers>

-- <vc-definitions>
def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  if n % 2 = 0 then true else false
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)

theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
  unfold isEven_postcond
  unfold isEven
  constructor
  · intro h
    by_cases h_mod : n % 2 = 0
    · exact h_mod
    · simp [h_mod] at h
  · intro h
    by_cases h_mod : n % 2 = 0
    · simp [h_mod] at h
    · exact h_mod
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 4
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 7
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 0
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": -2
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": -3
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/