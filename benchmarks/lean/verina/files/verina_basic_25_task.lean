/- 
-----Description-----
This task requires writing a Lean 4 method that calculates both the sum and the average of the first n natural numbers. The method should compute the sum of numbers from 0 to n (which equals n * (n + 1) / 2) and then determine the average by dividing this sum by n. The specification assumes that the input n is a positive integer.

-----Input-----
The input consists of:
n: A natural number representing the count of the first natural numbers. The value of n is assumed to be positive.

-----Output-----
The output is a pair consisting of:
- An integer representing the sum of the first n natural numbers.
- A floating-point number representing the average of the first n natural numbers.

-----Note-----
The input n must be a positive integer.
-/

@[reducible, simp]
def sumAndAverage_precond (n : Nat) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def sumAndAverage (n : Nat) (h_precond : sumAndAverage_precond (n)) : Int × Float :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def sumAndAverage_postcond (n : Nat) (result: Int × Float) (h_precond : sumAndAverage_precond (n)) :=
  (n = 0 → result == (0, 0.0)) ∧
  (n > 0 →
    result.1 == n * (n + 1) / 2 ∧
    result.2 == ((n * (n + 1) / 2).toFloat) / (n.toFloat))

theorem sumAndAverage_spec_satisfied (n: Nat) (h_precond : sumAndAverage_precond (n)) :
    sumAndAverage_postcond (n) (sumAndAverage (n) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 5
        },
        "expected": "(15, 3.0)",
        "unexpected": [
            "(14, 2.8)",
            "(16, 3.2)"
        ]
    },
    {
        "input": {
            "n": 1
        },
        "expected": "(1, 1.0)",
        "unexpected": [
            "(0, 0.0)",
            "(2, 2.0)"
        ]
    },
    {
        "input": {
            "n": 10
        },
        "expected": "(55, 5.5)",
        "unexpected": [
            "(50, 5.0)",
            "(60, 6.0)"
        ]
    },
    {
        "input": {
            "n": 0
        },
        "expected": "(0, 0.0)",
        "unexpected": [
            "(1, 0.1)",
            "(-1, -0.1)"
        ]
    },
    {
        "input": {
            "n": 2
        },
        "expected": "(3, 1.5)",
        "unexpected": [
            "(2, 1.0)",
            "(4, 2.0)"
        ]
    }
]
-/
