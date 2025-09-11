-- <vc-preamble>
@[reducible, simp]
def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isGreater (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isGreater_postcond (n : Int) (a : Array Int) (result: Bool) (h_precond : isGreater_precond (n) (a)) :=
  (∀ i, (hi : i < a.size) → n > a[i]) ↔ result

theorem isGreater_spec_satisfied (n: Int) (a: Array Int) (h_precond : isGreater_precond (n) (a)) :
    isGreater_postcond (n) (a) (isGreater (n) (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "n": 0,
            "a": "#[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "n": 6,
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 3,
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 5,
            "a": "#[5, 5, 5]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": -1,
            "a": "#[-10, -5, -3]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": -3,
            "a": "#[-1, -2, -3]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 0,
            "a": "#[0, -1, -2]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 10,
            "a": "#[1, 2, 9, 3]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    }
]
-/