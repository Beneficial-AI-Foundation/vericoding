/- 
-----Description-----
This task involves computing the integer square root of a given natural number. The goal is to determine the largest natural number r that satisfies r * r ≤ N and N < (r + 1) * (r + 1).

-----Input-----
The input consists of:
• N: A natural number.

-----Output-----
The output is a natural number r that meets the following conditions:
• r * r ≤ N
• N < (r + 1) * (r + 1)

-----Note-----
The implementation relies on a recursive strategy to iteratively increment r until (r + 1)*(r + 1) exceeds N. Edge cases, such as N = 0, should be handled correctly.
-/

@[reducible, simp]
def SquareRoot_precond (N : Nat) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def SquareRoot_postcond (N : Nat) (result: Nat) (h_precond : SquareRoot_precond (N)) :=
  result * result ≤ N ∧ N < (result + 1) * (result + 1)

theorem SquareRoot_spec_satisfied (N: Nat) (h_precond : SquareRoot_precond (N)) :
    SquareRoot_postcond (N) (SquareRoot (N) h_precond) h_precond := by
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
