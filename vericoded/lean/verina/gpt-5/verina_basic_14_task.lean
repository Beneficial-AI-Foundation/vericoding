import Mathlib
-- <vc-preamble>
@[reducible, simp]
def containsZ_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers required for this file.
-- </vc-helpers>

-- <vc-definitions>
def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  let cs := s.toList
  decide (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z'))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result

theorem containsZ_spec_satisfied (s: String) (h_precond : containsZ_precond (s)) :
    containsZ_postcond (s) (containsZ (s) h_precond) h_precond := by
  classical
  dsimp [containsZ_postcond, containsZ]
  by_cases hp : ∃ x, x ∈ s.toList ∧ (x = 'z' ∨ x = 'Z')
  · simp [hp]
  · simp [hp]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "hello"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": "zebra"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "Zebra"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": ""
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": "crazy"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "AZ"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "abc"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": "Zz"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "no letter"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/