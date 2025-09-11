-- <vc-preamble>
@[reducible, simp]
def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  k < s.size
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)

theorem removeElement_spec_satisfied (s: Array Int) (k: Nat) (h_precond : removeElement_precond (s) (k)) :
    removeElement_postcond (s) (k) (removeElement (s) (k) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "s": "#[1]",
            "k": 2
        }
    }
]
-- Tests
[
    {
        "input": {
            "s": "#[1, 2, 3, 4, 5]",
            "k": 2
        },
        "expected": "#[1, 2, 4, 5]",
        "unexpected": [
            "#[1, 2, 3, 5]",
            "#[1, 3, 4, 5]",
            "#[2, 3, 4, 5]"
        ]
    },
    {
        "input": {
            "s": "#[10, 20, 30, 40]",
            "k": 0
        },
        "expected": "#[20, 30, 40]",
        "unexpected": [
            "#[10, 30, 40]",
            "#[10, 20, 30, 40]",
            "#[20, 30, 40, 0]"
        ]
    },
    {
        "input": {
            "s": "#[10, 20, 30, 40]",
            "k": 3
        },
        "expected": "#[10, 20, 30]",
        "unexpected": [
            "#[20, 30, 40]",
            "#[10, 20, 40]",
            "#[10, 30, 40]"
        ]
    },
    {
        "input": {
            "s": "#[7]",
            "k": 0
        },
        "expected": "#[]",
        "unexpected": [
            "#[7]",
            "#[0]"
        ]
    }
]
-/