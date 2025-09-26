import Mathlib
-- <vc-preamble>
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  3 * x
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result

theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  unfold Triple_postcond Triple
  constructor
  · -- Prove (3 * x) / 3 = x
    rw [Int.mul_ediv_cancel_left x (by norm_num : (3 : Int) ≠ 0)]
  · -- Prove (3 * x) / 3 * 3 = 3 * x
    rw [Int.mul_ediv_cancel_left x (by norm_num : (3 : Int) ≠ 0)]
    rw [Int.mul_comm]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "x": 0
        },
        "expected": 0,
        "unexpected": [
            -1,
            1,
            2
        ]
    },
    {
        "input": {
            "x": 2
        },
        "expected": 6,
        "unexpected": [
            4,
            5,
            7
        ]
    },
    {
        "input": {
            "x": -4
        },
        "expected": -12,
        "unexpected": [
            -8,
            -10,
            -16
        ]
    },
    {
        "input": {
            "x": 10
        },
        "expected": 30,
        "unexpected": [
            20,
            25,
            35
        ]
    },
    {
        "input": {
            "x": -1
        },
        "expected": -3,
        "unexpected": [
            -2,
            -4,
            0
        ]
    }
]
-/