import Mathlib
-- <vc-preamble>
@[reducible, simp]
def allDigits_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def isDigit (c : Char) : Bool :=
  (c ≥ '0') && (c ≤ '9')
-- </vc-helpers>

-- <vc-definitions>
def allDigits (s : String) (h_precond : allDigits_precond (s)) : Bool :=
  s.toList.all isDigit
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def allDigits_postcond (s : String) (result: Bool) (h_precond : allDigits_precond (s)) :=
  (result = true ↔ ∀ c ∈ s.toList, isDigit c)

theorem allDigits_spec_satisfied (s: String) (h_precond : allDigits_precond (s)) :
    allDigits_postcond (s) (allDigits (s) h_precond) h_precond := by
  simp [allDigits_postcond, allDigits, List.all_eq_true]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "123456"
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "s": "123a56"
        },
        "expected": false,
        "unexpected": [true]
    },
    {
        "input": {
            "s": ""
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "s": "007"
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "s": "98 76"
        },
        "expected": false,
        "unexpected": [true]
    }
]
-/