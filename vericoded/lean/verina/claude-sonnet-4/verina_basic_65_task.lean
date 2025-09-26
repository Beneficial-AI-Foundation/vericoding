import Mathlib
-- <vc-preamble>
@[reducible, simp]
def SquareRoot_precond (N : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Use available square root theorems from Mathlib
-- Nat.sqrt is available, and we need the correct specification theorems
-- </vc-helpers>

-- <vc-definitions>
def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  Nat.sqrt N
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def SquareRoot_postcond (N : Nat) (result: Nat) (h_precond : SquareRoot_precond (N)) :=
  result * result ≤ N ∧ N < (result + 1) * (result + 1)

theorem SquareRoot_spec_satisfied (N: Nat) (h_precond : SquareRoot_precond (N)) :
    SquareRoot_postcond (N) (SquareRoot (N) h_precond) h_precond := by
  unfold SquareRoot_postcond SquareRoot
  constructor
  · exact Nat.sqrt_le N
  · exact Nat.lt_succ_sqrt N
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "N": 0
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "N": 1
        },
        "expected": 1,
        "unexpected": [
            0,
            2
        ]
    },
    {
        "input": {
            "N": 15
        },
        "expected": 3,
        "unexpected": [
            2,
            4,
            5
        ]
    },
    {
        "input": {
            "N": 16
        },
        "expected": 4,
        "unexpected": [
            3,
            5,
            6
        ]
    },
    {
        "input": {
            "N": 26
        },
        "expected": 5,
        "unexpected": [
            4,
            6,
            7
        ]
    }
]
-/