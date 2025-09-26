import Mathlib
-- <vc-preamble>
@[reducible, simp]
def lastDigit_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this simple case
-- </vc-helpers>

-- <vc-definitions>
def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  n % 10
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def lastDigit_postcond (n : Nat) (result: Nat) (h_precond : lastDigit_precond (n)) :=
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)

theorem lastDigit_spec_satisfied (n: Nat) (h_precond : lastDigit_precond (n)) :
    lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
  unfold lastDigit_postcond lastDigit
  constructor
  · constructor
    · exact Nat.zero_le (n % 10)
    · exact Nat.mod_lt n (by norm_num : 0 < 10)
  · constructor
    · simp
    · simp
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 123
        },
        "expected": 3,
        "unexpected": [
            2,
            1,
            23
        ]
    },
    {
        "input": {
            "n": 0
        },
        "expected": 0,
        "unexpected": [
            10,
            5,
            9
        ]
    },
    {
        "input": {
            "n": 987654321
        },
        "expected": 1,
        "unexpected": [
            9,
            0,
            2
        ]
    },
    {
        "input": {
            "n": 10
        },
        "expected": 0,
        "unexpected": [
            1,
            10,
            5
        ]
    },
    {
        "input": {
            "n": 999
        },
        "expected": 9,
        "unexpected": [
            8,
            99,
            0
        ]
    },
    {
        "input": {
            "n": 45
        },
        "expected": 5,
        "unexpected": [
            4,
            0,
            55
        ]
    },
    {
        "input": {
            "n": 100
        },
        "expected": 0,
        "unexpected": [
            1,
            10,
            5
        ]
    },
    {
        "input": {
            "n": 5
        },
        "expected": 5,
        "unexpected": [
            4,
            0,
            6
        ]
    }
]
-/