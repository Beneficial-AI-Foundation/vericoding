@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  sorry

@[reducible, simp]
def multiply_postcond (a : Int) (b : Int) (result: Int) (h_precond : multiply_precond (a) (b)) :=
  result - a * b = 0 ∧ a * b - result = 0

theorem multiply_spec_satisfied (a: Int) (b: Int) (h_precond : multiply_precond (a) (b)) :
    multiply_postcond (a) (b) (multiply (a) (b) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": 3,
            "b": 4
        },
        "expected": 12,
        "unexpected": [
            0,
            11,
            15
        ]
    },
    {
        "input": {
            "a": 3,
            "b": -4
        },
        "expected": -12,
        "unexpected": [
            0,
            -11,
            12
        ]
    },
    {
        "input": {
            "a": -3,
            "b": 4
        },
        "expected": -12,
        "unexpected": [
            0,
            -11,
            12
        ]
    },
    {
        "input": {
            "a": -3,
            "b": -4
        },
        "expected": 12,
        "unexpected": [
            0,
            11,
            -12
        ]
    },
    {
        "input": {
            "a": 0,
            "b": 5
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            5
        ]
    },
    {
        "input": {
            "a": 5,
            "b": 0
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            5
        ]
    },
    {
        "input": {
            "a": 0,
            "b": 0
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            5
        ]
    }
]
-/