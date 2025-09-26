import Mathlib
-- <vc-preamble>
@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  n % 2 = 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)

theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
  unfold isEven_postcond isEven
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    intro eq
    have : decide (n % 2 = 0) = true := decide_eq_true_iff.mpr eq
    exact h this
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