-- <vc-preamble>
import Mathlib

@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if h : x ≥ 0 then x else -x
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)

theorem Abs_spec_satisfied (x: Int) (h_precond : Abs_precond (x)) :
    Abs_postcond (x) (Abs (x) h_precond) h_precond := by
  unfold Abs_postcond Abs
  split_ifs with h
  · constructor
    · intro _; rfl
    · intro hlt; omega
  · constructor
    · intro hge; omega
    · intro _; ring
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "x": 5
        },
        "expected": 5,
        "unexpected": [
            -5,
            0,
            10
        ]
    },
    {
        "input": {
            "x": 0
        },
        "expected": 0,
        "unexpected": [
            -1,
            1,
            -5
        ]
    },
    {
        "input": {
            "x": -5
        },
        "expected": 5,
        "unexpected": [
            -5,
            -10,
            0
        ]
    },
    {
        "input": {
            "x": 10
        },
        "expected": 10,
        "unexpected": [
            -10,
            0,
            5
        ]
    },
    {
        "input": {
            "x": -10
        },
        "expected": 10,
        "unexpected": [
            -10,
            -1,
            0
        ]
    }
]
-/