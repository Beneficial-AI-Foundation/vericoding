@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def sumOfFourthPowerOfOddNumbers (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) : Nat :=
  sorry

@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :=
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)

theorem sumOfFourthPowerOfOddNumbers_spec_satisfied (n: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    sumOfFourthPowerOfOddNumbers_postcond (n) (sumOfFourthPowerOfOddNumbers (n) h_precond) h_precond := by
  sorry

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
            10
        ]
    },
    {
        "input": {
            "n": 1
        },
        "expected": 1,
        "unexpected": [
            2,
            0,
            5
        ]
    },
    {
        "input": {
            "n": 2
        },
        "expected": 82,
        "unexpected": [
            81,
            83,
            80
        ]
    },
    {
        "input": {
            "n": 3
        },
        "expected": 707,
        "unexpected": [
            706,
            708,
            700
        ]
    },
    {
        "input": {
            "n": 4
        },
        "expected": 3108,
        "unexpected": [
            3107,
            3109,
            3000
        ]
    },
    {
        "input": {
            "n": 5
        },
        "expected": 9669,
        "unexpected": [
            9668,
            9670,
            9000
        ]
    }
]
-/