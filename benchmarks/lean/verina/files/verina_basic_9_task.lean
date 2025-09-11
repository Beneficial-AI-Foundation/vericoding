-- <vc-preamble>
@[reducible, simp]
def hasCommonElement_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasCommonElement (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def hasCommonElement_postcond (a : Array Int) (b : Array Int) (result: Bool) (h_precond : hasCommonElement_precond (a) (b)) :=
  (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result

theorem hasCommonElement_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : hasCommonElement_precond (a) (b)) :
    hasCommonElement_postcond (a) (b) (hasCommonElement (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[]",
            "b": "#[]"
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
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[3, 4, 5]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[7, 8, 9]",
            "b": "#[10, 11, 7]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3, 4]",
            "b": "#[5, 6, 7, 8]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3, 4]",
            "b": "#[4, 5, 6]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[1, 1, 1]",
            "b": "#[1, 2, 1]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[0]",
            "b": "#[0]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[0]",
            "b": "#[-1, 1]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/