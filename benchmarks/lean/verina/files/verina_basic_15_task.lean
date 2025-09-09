import Mathlib

@[reducible, simp]
def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def containsConsecutiveNumbers (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) : Bool :=
  sorry

@[reducible, simp]
def containsConsecutiveNumbers_postcond (a : Array Int) (result: Bool) (h_precond : containsConsecutiveNumbers_precond (a)) :=
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result

theorem containsConsecutiveNumbers_spec_satisfied (a: Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    containsConsecutiveNumbers_postcond (a) (containsConsecutiveNumbers (a) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3, 5]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[1, 3, 5, 7]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[10]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[5, 6]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[5, 7, 8, 10]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[9, 9, 10]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[3, 3, 3]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/