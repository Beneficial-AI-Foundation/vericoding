-- <vc-preamble>
@[reducible, simp]
def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) (h_precond : hasOnlyOneDistinctElement_precond (a)) :=
  let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))

theorem hasOnlyOneDistinctElement_spec_satisfied (a: Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    hasOnlyOneDistinctElement_postcond (a) (hasOnlyOneDistinctElement (a) h_precond) h_precond := by
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
            "a": "#[1, 1, 1]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 1]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "a": "#[3, 4, 5, 6]"
        },
        "expected": false,
        "unexpected": [
            true
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
            "a": "#[0, 0, 0, 0]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "a": "#[0, 0, 1, 0]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/