-- <vc-preamble>
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)

theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
  sorry
-- </vc-theorems>

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