-- <vc-preamble>
@[reducible, simp]
def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : concat_precond (a) (b)) :=
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)

theorem concat_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : concat_precond (a) (b)) :
    concat_postcond (a) (b) (concat (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[4, 5]"
        },
        "expected": "#[1, 2, 3, 4, 5]",
        "unexpected": [
            "#[1, 2, 3, 5, 4]",
            "#[4, 5, 1, 2, 3]",
            "#[1, 2, 4, 3, 5]"
        ]
    },
    {
        "input": {
            "a": "#[]",
            "b": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[1]",
            "#[1, 2]"
        ]
    },
    {
        "input": {
            "a": "#[10]",
            "b": "#[20, 30, 40]"
        },
        "expected": "#[10, 20, 30, 40]",
        "unexpected": [
            "#[10, 20, 30]",
            "#[20, 30, 40, 10]"
        ]
    },
    {
        "input": {
            "a": "#[-1, -2]",
            "b": "#[0]"
        },
        "expected": "#[-1, -2, 0]",
        "unexpected": [
            "#[-1, 0, -2]",
            "#[0, -1, -2]"
        ]
    },
    {
        "input": {
            "a": "#[7, 8, 9]",
            "b": "#[]"
        },
        "expected": "#[7, 8, 9]",
        "unexpected": [
            "#[7, 8]",
            "#[8, 9]",
            "#[]"
        ]
    }
]
-/