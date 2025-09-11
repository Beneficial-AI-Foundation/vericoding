-- <vc-preamble>
@[reducible, simp]
def maxArray_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
def maxArray_aux (a : Array Int) (index : Nat) (current : Int) : Int :=
  if index < a.size then
    let new_current := if current > a[index]! then current else a[index]!
    maxArray_aux a (index + 1) new_current
  else
    current
-- </vc-helpers>

-- <vc-definitions>
def maxArray (a : Array Int) (h_precond : maxArray_precond (a)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxArray_postcond (a : Array Int) (result: Int) (h_precond : maxArray_precond (a)) :=
  (∀ (k : Nat), k < a.size → result >= a[k]!) ∧ (∃ (k : Nat), k < a.size ∧ result = a[k]!)

theorem maxArray_spec_satisfied (a: Array Int) (h_precond : maxArray_precond (a)) :
    maxArray_postcond (a) (maxArray (a) h_precond) h_precond := by
  sorry
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
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": 5,
        "unexpected": [
            4,
            3
        ]
    },
    {
        "input": {
            "a": "#[5, 3, 4, 1, 2]"
        },
        "expected": 5,
        "unexpected": [
            4,
            3,
            2
        ]
    },
    {
        "input": {
            "a": "#[7]"
        },
        "expected": 7,
        "unexpected": [
            6,
            8
        ]
    },
    {
        "input": {
            "a": "#[-1, -5, -3, -4]"
        },
        "expected": -1,
        "unexpected": [
            -3,
            -4
        ]
    },
    {
        "input": {
            "a": "#[-10, -20, -30, -5, -15]"
        },
        "expected": -5,
        "unexpected": [
            -10,
            -15,
            -20
        ]
    }
]
-/