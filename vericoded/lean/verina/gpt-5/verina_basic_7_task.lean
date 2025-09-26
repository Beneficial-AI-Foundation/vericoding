import Mathlib
-- <vc-preamble>
@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem nat_sub_self (a : Nat) : a - a = 0 := Nat.sub_self a
-- </vc-helpers>

-- <vc-definitions>
def sumOfSquaresOfFirstNOddNumbers (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  (n * (2 * n - 1) * (2 * n + 1)) / 3
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :=
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0

theorem sumOfSquaresOfFirstNOddNumbers_spec_satisfied (n: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    sumOfSquaresOfFirstNOddNumbers_postcond (n) (sumOfSquaresOfFirstNOddNumbers (n) h_precond) h_precond := by
  dsimp [sumOfSquaresOfFirstNOddNumbers_postcond, sumOfSquaresOfFirstNOddNumbers]
  constructor <;> simp
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 0
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "n": 1
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            3
        ]
    },
    {
        "input": {
            "n": 2
        },
        "expected": 10,
        "unexpected": [
            9,
            11,
            12
        ]
    },
    {
        "input": {
            "n": 3
        },
        "expected": 35,
        "unexpected": [
            30,
            34,
            36
        ]
    },
    {
        "input": {
            "n": 4
        },
        "expected": 84,
        "unexpected": [
            80,
            85,
            90
        ]
    },
    {
        "input": {
            "n": 5
        },
        "expected": 165,
        "unexpected": [
            160,
            166,
            170
        ]
    },
    {
        "input": {
            "n": 10
        },
        "expected": 1330,
        "unexpected": [
            1320,
            1331,
            1340
        ]
    }
]
-/