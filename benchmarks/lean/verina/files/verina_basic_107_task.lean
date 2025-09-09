@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  sorry

@[reducible, simp]
def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  2 * result = a + b - ((a + b) % 2)

theorem ComputeAvg_spec_satisfied (a: Int) (b: Int) (h_precond : ComputeAvg_precond (a) (b)) :
    ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": 4,
            "b": 6
        },
        "expected": 5,
        "unexpected": [
            4,
            6,
            7
        ]
    },
    {
        "input": {
            "a": 3,
            "b": 5
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
            "a": 3,
            "b": 4
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
            "a": -3,
            "b": 7
        },
        "expected": 2,
        "unexpected": [
            1,
            3,
            0
        ]
    },
    {
        "input": {
            "a": -5,
            "b": 5
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            2
        ]
    }
]
-/