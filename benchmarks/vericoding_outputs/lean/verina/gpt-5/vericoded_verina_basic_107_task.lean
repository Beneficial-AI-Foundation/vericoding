import Mathlib
-- <vc-preamble>
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma two_mul_ediv_eq_sub_emod (x : Int) : 2 * (x / 2) = x - x % 2 := by
  have h' : 2 * (x / 2) + x % 2 = x := by
    have := Int.emod_add_ediv x 2
    simpa [add_comm] using this
  exact (eq_sub_iff_add_eq).2 h'

-- </vc-helpers>

-- <vc-definitions>
def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  (a + b) / 2
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  2 * result = a + b - ((a + b) % 2)

theorem ComputeAvg_spec_satisfied (a: Int) (b: Int) (h_precond : ComputeAvg_precond (a) (b)) :
    ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
  unfold ComputeAvg_postcond ComputeAvg
  simpa using two_mul_ediv_eq_sub_emod (a + b)
-- </vc-theorems>

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