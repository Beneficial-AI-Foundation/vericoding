import Mathlib
-- <vc-preamble>
@[reducible, simp]
def iter_copy_precond (s : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this verification task.
-- </vc-helpers>

-- <vc-definitions>
def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  s
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def iter_copy_postcond (s : Array Int) (result: Array Int) (h_precond : iter_copy_precond (s)) :=
  (s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)

theorem iter_copy_spec_satisfied (s: Array Int) (h_precond : iter_copy_precond (s)) :
    iter_copy_postcond (s) (iter_copy (s) h_precond) h_precond := by
  constructor
  · simp [iter_copy]
  · intro i hi
    simp [iter_copy]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "#[1, 2, 3]"
        },
        "expected": "#[1, 2, 3]",
        "unexpected": [
            "#[1, 3, 2]",
            "#[1, 2]"
        ]
    },
    {
        "input": {
            "s": "#[10, 20, 30, 40]"
        },
        "expected": "#[10, 20, 30, 40]",
        "unexpected": [
            "#[10, 20, 30]",
            "#[10, 20, 40, 30]"
        ]
    },
    {
        "input": {
            "s": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[0]",
            "#[1]"
        ]
    },
    {
        "input": {
            "s": "#[-1, -2, -3]"
        },
        "expected": "#[-1, -2, -3]",
        "unexpected": [
            "#[-1, -3, -2]",
            "#[-1, -2]"
        ]
    },
    {
        "input": {
            "s": "#[5, 5, 5, 5]"
        },
        "expected": "#[5, 5, 5, 5]",
        "unexpected": [
            "#[5, 5, 5]",
            "#[5, 5, 5, 0]",
            "#[0, 5, 5, 5]"
        ]
    }
]
-/