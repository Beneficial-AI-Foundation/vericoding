/- 
-----Description-----
This task requires writing a Lean 4 method that finds the maximum among three given integers. The method should return the largest value, ensuring that the result is greater than or equal to each of the input numbers and that it is one of the provided integers.

-----Input-----
The input consists of three integers:
a: The first integer.
b: The second integer.
c: The third integer.

-----Output-----
The output is an integer:
Returns the maximum of the three input numbers, assuring that the returned value is greater than or equal to a, b, and c, and that it matches one of these values.
-/

@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)

theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
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
            "a": 3,
            "b": 2,
            "c": 1
        },
        "expected": 3,
        "unexpected": [
            2,
            1,
            -1
        ]
    },
    {
        "input": {
            "a": 5,
            "b": 5,
            "c": 5
        },
        "expected": 5,
        "unexpected": [
            6,
            4
        ]
    },
    {
        "input": {
            "a": 10,
            "b": 20,
            "c": 15
        },
        "expected": 20,
        "unexpected": [
            10,
            15
        ]
    },
    {
        "input": {
            "a": -1,
            "b": -2,
            "c": -3
        },
        "expected": -1,
        "unexpected": [
            -2,
            -3
        ]
    },
    {
        "input": {
            "a": 0,
            "b": -10,
            "c": -5
        },
        "expected": 0,
        "unexpected": [
            -5,
            -10
        ]
    }
]
-/
