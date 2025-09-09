import Mathlib

@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  sorry

@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)

theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[1, 3, 5, 7, 9]",
            "e": 5
        },
        "expected": "2",
        "unexpected": [
            "1",
            "3",
            "4"
        ]
    },
    {
        "input": {
            "a": "#[2, 4, 6, 8]",
            "e": 5
        },
        "expected": "4",
        "unexpected": [
            "1",
            "3",
            "5"
        ]
    },
    {
        "input": {
            "a": "#[5, 5, 5]",
            "e": 5
        },
        "expected": "0",
        "unexpected": [
            "1",
            "2",
            "3"
        ]
    },
    {
        "input": {
            "a": "#[10, 9, 8, 7]",
            "e": 10
        },
        "expected": "0",
        "unexpected": [
            "1",
            "2",
            "3"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3, 3, 4]",
            "e": 3
        },
        "expected": "2",
        "unexpected": [
            "1",
            "3",
            "4"
        ]
    }
]
-/