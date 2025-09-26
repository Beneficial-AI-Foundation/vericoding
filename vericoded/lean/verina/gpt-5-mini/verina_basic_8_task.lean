import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myMin_precond (a : Int) (b : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def myMin_aux (a b : Int) : Int := if a ≤ b then a else b

-- LLM HELPER
theorem myMin_aux_spec (a b : Int) : (myMin_aux a b ≤ a ∧ myMin_aux a b ≤ b) ∧ (myMin_aux a b = a ∨ myMin_aux a b = b) := by
  dsimp [myMin_aux]
  split_ifs with h
  · constructor
    · constructor
      · exact le_refl a
      · exact h
    · left; rfl
  · have hb := Or.resolve_left (le_total a b) h
    constructor
    · constructor
      · exact hb
      · exact le_refl b
    · right; rfl
-- </vc-helpers>

-- <vc-definitions>
def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  myMin_aux a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myMin_postcond (a : Int) (b : Int) (result: Int) (h_precond : myMin_precond (a) (b)) :=
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)

theorem myMin_spec_satisfied (a: Int) (b: Int) (h_precond : myMin_precond (a) (b)) :
    myMin_postcond (a) (b) (myMin (a) (b) h_precond) h_precond := by
  dsimp [myMin]
  exact myMin_aux_spec a b
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": 3,
            "b": 5
        },
        "expected": 3,
        "unexpected": [
            5,
            4,
            8
        ]
    },
    {
        "input": {
            "a": 10,
            "b": 7
        },
        "expected": 7,
        "unexpected": [
            10,
            8,
            9
        ]
    },
    {
        "input": {
            "a": 4,
            "b": 4
        },
        "expected": 4,
        "unexpected": [
            0,
            8,
            2
        ]
    },
    {
        "input": {
            "a": -3,
            "b": 5
        },
        "expected": -3,
        "unexpected": [
            5,
            0,
            -5
        ]
    },
    {
        "input": {
            "a": 3,
            "b": -5
        },
        "expected": -5,
        "unexpected": [
            3,
            0,
            -3
        ]
    },
    {
        "input": {
            "a": -3,
            "b": -5
        },
        "expected": -5,
        "unexpected": [
            -3,
            0,
            -1
        ]
    },
    {
        "input": {
            "a": 0,
            "b": 10
        },
        "expected": 0,
        "unexpected": [
            10,
            1,
            -1
        ]
    },
    {
        "input": {
            "a": 0,
            "b": -10
        },
        "expected": -10,
        "unexpected": [
            0,
            -1,
            -5
        ]
    }
]
-/