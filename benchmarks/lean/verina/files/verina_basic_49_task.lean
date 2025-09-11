-- <vc-preamble>
@[reducible, simp]
def findFirstOdd_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)

theorem findFirstOdd_spec_satisfied (a: Array Int) (h_precond : findFirstOdd_precond (a)) :
    findFirstOdd_postcond (a) (findFirstOdd (a) h_precond) h_precond := by
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
            "a": "#[2, 4, 6, 8]"
        },
        "expected": "none",
        "unexpected": [
            "some (0)"
        ]
    },
    {
        "input": {
            "a": "#[3, 4, 6, 8]"
        },
        "expected": "some (0)",
        "unexpected": [
            "some (1)",
            "some (2)",
            "none"
        ]
    },
    {
        "input": {
            "a": "#[2, 4, 5, 8]"
        },
        "expected": "some (2)",
        "unexpected": [
            "some (0)",
            "some (1)",
            "some (3)",
            "none"
        ]
    },
    {
        "input": {
            "a": "#[7]"
        },
        "expected": "some (0)",
        "unexpected": [
            "some (1)",
            "none"
        ]
    },
    {
        "input": {
            "a": "#[2]"
        },
        "expected": "none",
        "unexpected": [
            "some (0)"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3]"
        },
        "expected": "some (0)",
        "unexpected": [
            "some (1)",
            "some (2)",
            "none"
        ]
    }
]
-/