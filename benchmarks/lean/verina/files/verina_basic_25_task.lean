@[reducible, simp]
def sumAndAverage_precond (n : Nat) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def sumAndAverage (n : Nat) (h_precond : sumAndAverage_precond (n)) : Int × Float :=
  sorry

@[reducible, simp]
def sumAndAverage_postcond (n : Nat) (result: Int × Float) (h_precond : sumAndAverage_precond (n)) :=
  (n = 0 → result == (0, 0.0)) ∧
  (n > 0 →
    result.1 == n * (n + 1) / 2 ∧
    result.2 == ((n * (n + 1) / 2).toFloat) / (n.toFloat))

theorem sumAndAverage_spec_satisfied (n: Nat) (h_precond : sumAndAverage_precond (n)) :
    sumAndAverage_postcond (n) (sumAndAverage (n) h_precond) h_precond := by
  sorry

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