@[reducible, simp]
def isSublist_precond (sub : List Int) (main : List Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  sorry

@[reducible, simp]
def isSublist_postcond (sub : List Int) (main : List Int) (result: Bool) (h_precond : isSublist_precond (sub) (main)) :=
  (∃ i, i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length) ↔ result

theorem isSublist_spec_satisfied (sub: List Int) (main: List Int) (h_precond : isSublist_precond (sub) (main)) :
    isSublist_postcond (sub) (main) (isSublist (sub) (main) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "sub": "[1, 2]",
            "main": "[3, 1, 2, 4]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "sub": "[2, 3]",
            "main": "[3, 1, 2, 4]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "sub": "[3, 1]",
            "main": "[3, 1, 2, 4]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "sub": "[4]",
            "main": "[3, 1, 2, 4]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "sub": "[5]",
            "main": "[3, 1, 2, 4]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "sub": "[]",
            "main": "[3, 1, 2, 4]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "sub": "[1, 2]",
            "main": "[]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "sub": "[]",
            "main": "[]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    }
]
-/