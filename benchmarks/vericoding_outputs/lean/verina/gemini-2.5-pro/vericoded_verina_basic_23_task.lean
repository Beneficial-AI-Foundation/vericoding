import Mathlib
-- <vc-preamble>
@[reducible, simp]
def differenceMinMax_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def array_min (a : Array Int) : Int :=
  a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)

-- LLM HELPER
def array_max (a : Array Int) : Int :=
  a.foldl (fun acc x => if x > acc then x else acc) (a[0]!)
-- </vc-helpers>

-- <vc-definitions>
def differenceMinMax (a : Array Int) (h_precond : differenceMinMax_precond (a)) : Int :=
  array_max a - array_min a
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def differenceMinMax_postcond (a : Array Int) (result: Int) (h_precond : differenceMinMax_precond (a)) :=
  result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))

theorem differenceMinMax_spec_satisfied (a: Array Int) (h_precond : differenceMinMax_precond (a)) :
    differenceMinMax_postcond (a) (differenceMinMax (a) h_precond) h_precond := by
  simp [differenceMinMax, array_min, array_max, differenceMinMax_postcond]
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]"
        },
        "expected": 8,
        "unexpected": [
            7,
            9,
            10
        ]
    },
    {
        "input": {
            "a": "#[10, 20, 30, 40, 50]"
        },
        "expected": 40,
        "unexpected": [
            30,
            35,
            45
        ]
    },
    {
        "input": {
            "a": "#[-10, -20, -30, -40, -50]"
        },
        "expected": 40,
        "unexpected": [
            30,
            41,
            20
        ]
    },
    {
        "input": {
            "a": "#[7]"
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            2
        ]
    },
    {
        "input": {
            "a": "#[5, 5, 5, 5]"
        },
        "expected": 0,
        "unexpected": [
            1,
            5,
            -1
        ]
    },
    {
        "input": {
            "a": "#[1, -1, 2, -2]"
        },
        "expected": 4,
        "unexpected": [
            3,
            0,
            5
        ]
    }
]
-/