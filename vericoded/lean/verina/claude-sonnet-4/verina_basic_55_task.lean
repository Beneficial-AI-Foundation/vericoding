import Mathlib
-- <vc-preamble>
@[reducible, simp]
def Compare_precond (a : Int) (b : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple comparison
-- </vc-helpers>

-- <vc-definitions>
def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  if a = b then true else false
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Compare_postcond (a : Int) (b : Int) (result: Bool) (h_precond : Compare_precond (a) (b)) :=
  (a = b → result = true) ∧ (a ≠ b → result = false)

theorem Compare_spec_satisfied (a: Int) (b: Int) (h_precond : Compare_precond (a) (b)) :
    Compare_postcond (a) (b) (Compare (a) (b) h_precond) h_precond := by
  unfold Compare_postcond Compare
  constructor
  · intro h_eq
    simp [h_eq]
  · intro h_neq
    simp [if_neg h_neq]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": 1,
            "b": 1
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": 1,
            "b": 2
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/