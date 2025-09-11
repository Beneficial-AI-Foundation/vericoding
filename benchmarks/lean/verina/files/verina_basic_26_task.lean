-- <vc-preamble>
@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)

theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 4
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 7
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 0
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": -2
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": -3
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/