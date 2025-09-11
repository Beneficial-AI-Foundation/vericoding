-- <vc-preamble>
@[reducible, simp]
def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  ∃ i, i < a.size ∧ P (a[i]!)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def LinearSearch3_postcond (a : Array Int) (P : Int -> Bool) (result: Nat) (h_precond : LinearSearch3_precond (a) (P)) :=
  result < a.size ∧ P (a[result]!) ∧ (∀ k, k < result → ¬ P (a[k]!))

theorem LinearSearch3_spec_satisfied (a: Array Int) (P: Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    LinearSearch3_postcond (a) (P) (LinearSearch3 (a) (P) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]",
            "P": "fun x => x > 10"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[4, 7, 2, 9]",
            "P": "fun x => x > 5"
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            3
        ]
    },
    {
        "input": {
            "a": "#[10, 8, 6, 4, 2]",
            "P": "fun x => x < 5"
        },
        "expected": 3,
        "unexpected": [
            0,
            1,
            4
        ]
    },
    {
        "input": {
            "a": "#[5, 3, 1, 2]",
            "P": "fun x => x == 1"
        },
        "expected": 2,
        "unexpected": [
            0,
            1,
            3
        ]
    },
    {
        "input": {
            "a": "#[0, 1, 2, 3]",
            "P": "fun x => x == 0"
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            3
        ]
    },
    {
        "input": {
            "a": "#[9, 9, 9, 9]",
            "P": "fun x => x == 9"
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            3
        ]
    }
]
-/