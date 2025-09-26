import Mathlib
-- <vc-preamble>
@[reducible, simp]
def ToArray_precond (xs : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- no helpers required
-- </vc-helpers>

-- <vc-definitions>
def ToArray (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  xs.toArray
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def ToArray_postcond (xs : List Int) (result: Array Int) (h_precond : ToArray_precond (xs)) :=
  result.size = xs.length ∧ ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!

theorem ToArray_spec_satisfied (xs: List Int) (h_precond : ToArray_precond (xs)) :
    ToArray_postcond (xs) (ToArray (xs) h_precond) h_precond := by
    classical
  dsimp [ToArray, ToArray_postcond]
  constructor
  · simpa
  · intro i hi
    simpa [Array.get!, List.get!]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "xs": "[1, 2, 3]"
        },
        "expected": "#[1, 2, 3]",
        "unexpected": [
            "#[1, 2]",
            "#[1, 2, 3, 4]",
            "#[3, 2, 1]"
        ]
    },
    {
        "input": {
            "xs": "[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[0]",
            "#[1]",
            "#[1, 0]"
        ]
    },
    {
        "input": {
            "xs": "[0, -1, 5]"
        },
        "expected": "#[0, -1, 5]",
        "unexpected": [
            "#[-1, 0, 5]",
            "#[0, 5]",
            "#[0, -1, 4]"
        ]
    },
    {
        "input": {
            "xs": "[7]"
        },
        "expected": "#[7]",
        "unexpected": [
            "#[]",
            "#[0, 7]",
            "#[8]"
        ]
    },
    {
        "input": {
            "xs": "[100, 200, 300, 400]"
        },
        "expected": "#[100, 200, 300, 400]",
        "unexpected": [
            "#[100, 200, 300]",
            "#[100, 300, 200, 400]",
            "#[400, 300, 200, 100]"
        ]
    }
]
-/