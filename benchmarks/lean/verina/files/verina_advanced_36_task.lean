-- <vc-preamble>
@[reducible]
def majorityElement_precond (xs : List Nat) : Prop :=
  xs.length > 0 ∧ xs.any (fun x => xs.count x > xs.length / 2)
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def majorityElement (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def majorityElement_postcond (xs : List Nat) (result: Nat) (h_precond : majorityElement_precond (xs)) : Prop :=
  let count := xs.count result
  count > xs.length / 2

theorem majorityElement_spec_satisfied (xs: List Nat) (h_precond : majorityElement_precond (xs)) :
    majorityElement_postcond (xs) (majorityElement (xs) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "xs": "[1, 2, 3]"
        }
    },
    {
        "input": {
            "xs": "[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "xs": "[3, 3, 4, 2, 3, 3, 3]"
        },
        "expected": 3,
        "unexpected": [
            2,
            4
        ]
    },
    {
        "input": {
            "xs": "[1, 1, 2, 1, 3, 1, 1]"
        },
        "expected": 1,
        "unexpected": [
            2,
            3
        ]
    },
    {
        "input": {
            "xs": "[2, 2, 2, 1, 1]"
        },
        "expected": 2,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "xs": "[9, 9, 9, 9, 1, 2, 3]"
        },
        "expected": 9,
        "unexpected": [
            1,
            2,
            3
        ]
    },
    {
        "input": {
            "xs": "[5, 5, 5, 5, 5, 6, 7]"
        },
        "expected": 5,
        "unexpected": [
            6,
            7
        ]
    }
]
-/