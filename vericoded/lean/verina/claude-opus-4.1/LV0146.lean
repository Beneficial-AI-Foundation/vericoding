-- <vc-preamble>
import Mathlib

@[reducible, simp]
def ComputeIsEven_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  x % 2 = 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  result = true ↔ ∃ k : Int, x = 2 * k

theorem ComputeIsEven_spec_satisfied (x: Int) (h_precond : ComputeIsEven_precond (x)) :
    ComputeIsEven_postcond (x) (ComputeIsEven (x) h_precond) h_precond := by
  unfold ComputeIsEven_postcond ComputeIsEven
  constructor
  · intro h
    have h_eq : x % 2 = 0 := by
      simp only [decide_eq_true_eq] at h
      exact h
    use x / 2
    have : x = 2 * (x / 2) + x % 2 := (Int.ediv_add_emod x 2).symm
    rw [h_eq] at this
    simp at this
    exact this
  · intro ⟨k, hk⟩
    rw [hk]
    simp [Int.mul_emod_right]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "x": 4
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": 7
        },
        "expected": false,
        "unexpected": [true]
    },
    {
        "input": {
            "x": 0
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": -2
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": -3
        },
        "expected": false,
        "unexpected": [true]
    }
]
-/