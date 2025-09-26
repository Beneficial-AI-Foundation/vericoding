import Mathlib
-- <vc-preamble>
@[reducible]
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  digits.all (fun d => d = 0 ∨ d = 1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper lemmas for binary to decimal conversion
lemma foldl_eq_self_sub_zero (n : Nat) : n - 0 = n := by simp
lemma zero_sub_self (n : Nat) : 0 - n = 0 := by simp
-- </vc-helpers>

-- <vc-definitions>
def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0

theorem binaryToDecimal_spec_satisfied (digits: List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    binaryToDecimal_postcond (digits) (binaryToDecimal (digits) h_precond) h_precond := by
  unfold binaryToDecimal_postcond binaryToDecimal
  constructor
  · simp
  · simp
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "digits": "[2]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "digits": "[1, 0, 1]"
        },
        "expected": 5,
        "unexpected": [
            3,
            4,
            6
        ]
    },
    {
        "input": {
            "digits": "[1, 1, 1, 1]"
        },
        "expected": 15,
        "unexpected": [
            14,
            16
        ]
    },
    {
        "input": {
            "digits": "[0, 0, 0]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "digits": "[1, 0, 0, 0, 0]"
        },
        "expected": 16,
        "unexpected": [
            8,
            0
        ]
    },
    {
        "input": {
            "digits": "[]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "digits": "[1]"
        },
        "expected": 1,
        "unexpected": [
            0
        ]
    }
]
-/