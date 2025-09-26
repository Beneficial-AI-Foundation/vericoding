import Mathlib
-- <vc-preamble>
@[reducible, simp]
def containsZ_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  s.toList.any (fun c => decide (c = 'z' ∨ c = 'Z'))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result

theorem containsZ_spec_satisfied (s: String) (h_precond : containsZ_precond (s)) :
    containsZ_postcond (s) (containsZ (s) h_precond) h_precond := by
  simp [containsZ, containsZ_postcond, List.any_eq_true, decide_eq_true_iff]
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