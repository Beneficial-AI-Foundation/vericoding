import Mathlib
-- <vc-preamble>
@[reducible, simp]
def elementWiseModulo_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size ∧ a.size > 0 ∧
  (∀ i, i < b.size → b[i]! ≠ 0)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helper code needed for this verification
-- </vc-helpers>

-- <vc-definitions>
def elementWiseModulo (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) : Array Int :=
  Array.ofFn (fun i : Fin a.size => a[(i : Nat)]! % b[(i : Nat)]!)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def elementWiseModulo_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :=
  result.size = a.size ∧
  (∀ i, i < result.size → result[i]! = a[i]! % b[i]!)

theorem elementWiseModulo_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    elementWiseModulo_postcond (a) (b) (elementWiseModulo (a) (b) h_precond) h_precond := by
  classical
constructor
· simp [elementWiseModulo]
· intro i hi
  have hi' : i < a.size := by simpa [elementWiseModulo] using hi
  simpa [elementWiseModulo, hi']
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[1]",
            "b": "#[4, 0]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[10, 20, 30]",
            "b": "#[3, 7, 5]"
        },
        "expected": "#[1, 6, 0]",
        "unexpected": [
            "#[1, 0, 0]",
            "#[0, 6, 0]"
        ]
    },
    {
        "input": {
            "a": "#[100, 200, 300, 400]",
            "b": "#[10, 20, 30, 50]"
        },
        "expected": "#[0, 0, 0, 0]",
        "unexpected": [
            "#[0, 0, 0, 1]",
            "#[1, 0, 0, 0]"
        ]
    },
    {
        "input": {
            "a": "#[-10, -20, 30]",
            "b": "#[3, -7, 5]"
        },
        "expected": "#[2, 1, 0]",
        "unexpected": [
            "#[-1, -5, 0]",
            "#[-1, -6, 1]",
            "#[0, -6, 0]"
        ]
    }
]
-/