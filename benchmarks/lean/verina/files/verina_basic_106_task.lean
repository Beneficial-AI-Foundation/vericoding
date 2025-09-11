-- <vc-preamble>
@[reducible, simp]
def arraySum_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arraySum (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arraySum_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arraySum_precond (a) (b)) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → a[i]! + b[i]! = result[i]!)

theorem arraySum_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arraySum_precond (a) (b)) :
    arraySum_postcond (a) (b) (arraySum (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[1, 2, 3, 4]",
            "b": "#[5, 6, 7]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[4, 5, 6]"
        },
        "expected": "#[5, 7, 9]",
        "unexpected": [
            "#[5, 6, 9]",
            "#[4, 7, 9]"
        ]
    },
    {
        "input": {
            "a": "#[0, 0, 0]",
            "b": "#[0, 0, 0]"
        },
        "expected": "#[0, 0, 0]",
        "unexpected": [
            "#[0, 0, 1]",
            "#[1, 0, 0]"
        ]
    },
    {
        "input": {
            "a": "#[-1, 2, 3]",
            "b": "#[1, -2, 4]"
        },
        "expected": "#[0, 0, 7]",
        "unexpected": [
            "#[0, 1, 7]",
            "#[0, 0, 6]"
        ]
    },
    {
        "input": {
            "a": "#[10]",
            "b": "#[-10]"
        },
        "expected": "#[0]",
        "unexpected": [
            "#[1]",
            "#[-1]"
        ]
    },
    {
        "input": {
            "a": "#[100, 200, 300]",
            "b": "#[100, 200, 300]"
        },
        "expected": "#[200, 400, 600]",
        "unexpected": [
            "#[200, 400, 601]",
            "#[199, 400, 600]",
            "#[200, 399, 600]"
        ]
    }
]
-/