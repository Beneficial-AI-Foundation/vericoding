/- 
-----Description-----
This task requires writing a Lean 4 method that determines whether a given integer is even. In other words, the method should return true if the number is even and false if the number is odd.

-----Input-----
The input consists of:
n: An integer.

-----Output-----
The output is a Boolean value:
Returns true if the input number is even.
Returns false if the input number is odd.

-----Note-----
There are no preconditions; the method will always work for any integer input.
-/

@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)

theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
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
            "n": 4
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 7
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 0
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": -2
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": -3
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/