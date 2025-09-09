@[reducible, simp]
def isSorted_precond (a : Array Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  sorry

@[reducible, simp]
def isSorted_postcond (a : Array Int) (result: Bool) (h_precond : isSorted_precond (a)) :=
  (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result

theorem isSorted_spec_satisfied (a: Array Int) (h_precond : isSorted_precond (a)) :
    isSorted_postcond (a) (isSorted (a) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[5, 4, 3, 2, 1]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[1, 3, 2, 4, 5]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[10]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[2, 2, 2, 2]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 2, 3]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    }
]
-/