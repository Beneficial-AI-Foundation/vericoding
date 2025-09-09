@[reducible, simp]
def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  True

-- <vc-helpers>
def isOdd (n : Int) : Bool :=
  n % 2 == 1
-- </vc-helpers>

def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
  sorry

@[reducible, simp]
def isOddAtIndexOdd_postcond (a : Array Int) (result: Bool) (h_precond : isOddAtIndexOdd_precond (a)) :=
  result ↔ (∀ i, (hi : i < a.size) → isOdd i → isOdd (a[i]))

theorem isOddAtIndexOdd_spec_satisfied (a: Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    isOddAtIndexOdd_postcond (a) (isOddAtIndexOdd (a) h_precond) h_precond := by
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
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[1, 3, 5, 7, 9]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[2, 4, 6, 8, 10]"
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
            "a": "#[7]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[0, 1, 0, 1]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[0, 2, 4, 6]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/