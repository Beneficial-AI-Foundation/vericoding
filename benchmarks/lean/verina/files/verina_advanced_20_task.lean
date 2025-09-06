/- 
-----Description-----
This task requires writing a Lean 4 method that returns true if the input n is divisible by 8 or has 8 as one of it's digits.

-----Input-----
The input consists of one integer:
n: The main integer.

-----Output-----
The output is an boolean:
Returns true if the input is divisible by 8 or has 8 as one of it's digits.
-/

@[reducible]
def isItEight_precond (n : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def isItEight (n : Int) (h_precond : isItEight_precond (n)) : Bool :=
  sorry

@[reducible]
def isItEight_postcond (n : Int) (result: Bool) (h_precond : isItEight_precond (n)) : Prop :=
  let absN := Int.natAbs n;
  (n % 8 == 0 ∨ ∃ i, absN / (10^i) % 10 == 8) ↔ result

theorem isItEight_spec_satisfied (n: Int) (h_precond : isItEight_precond (n)) :
    isItEight_postcond (n) (isItEight (n) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 8
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 98
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 1224
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 73
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 208
        },
        "expected": true,
        "unexpected": [
            false
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
            "n": -123456780
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 1
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": -9999
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": -123453
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/