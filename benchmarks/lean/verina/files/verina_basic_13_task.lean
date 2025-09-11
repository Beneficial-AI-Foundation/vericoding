-- <vc-preamble>
@[reducible, simp]
def cubeElements_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cubeElements (a : Array Int) (h_precond : cubeElements_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def cubeElements_postcond (a : Array Int) (result: Array Int) (h_precond : cubeElements_precond (a)) :=
  (result.size = a.size) ∧
  (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!)

theorem cubeElements_spec_satisfied (a: Array Int) (h_precond : cubeElements_precond (a)) :
    cubeElements_postcond (a) (cubeElements (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3, 4]"
        },
        "expected": "#[1, 8, 27, 64]",
        "unexpected": [
            "#[1, 4, 9, 16]",
            "#[1, 8, 27, 63]",
            "#[0, 0, 0, 0]"
        ]
    },
    {
        "input": {
            "a": "#[0, -1, -2, 3]"
        },
        "expected": "#[0, -1, -8, 27]",
        "unexpected": [
            "#[0, 1, 8, -27]",
            "#[0, -1, -8, 26]",
            "#[1, -1, -8, 27]"
        ]
    },
    {
        "input": {
            "a": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[1]",
            "#[-1]",
            "#[0]"
        ]
    },
    {
        "input": {
            "a": "#[5]"
        },
        "expected": "#[125]",
        "unexpected": [
            "#[5]",
            "#[25]",
            "#[0]"
        ]
    },
    {
        "input": {
            "a": "#[-3, -3]"
        },
        "expected": "#[-27, -27]",
        "unexpected": [
            "#[27, 27]",
            "#[-9, -9]",
            "#[-27, 27]"
        ]
    }
]
-/