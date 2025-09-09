@[reducible, simp]
def TestArrayElements_precond (a : Array Int) (j : Nat) : Prop :=
  j < a.size

-- <vc-helpers>
-- </vc-helpers>

def TestArrayElements (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) : Array Int :=
  sorry

@[reducible, simp]
def TestArrayElements_postcond (a : Array Int) (j : Nat) (result: Array Int) (h_precond : TestArrayElements_precond (a) (j)) :=
  (result[j]! = 60) ∧ (∀ k, k < a.size → k ≠ j → result[k]! = a[k]!)

theorem TestArrayElements_spec_satisfied (a: Array Int) (j: Nat) (h_precond : TestArrayElements_precond (a) (j)) :
    TestArrayElements_postcond (a) (j) (TestArrayElements (a) (j) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[1, 2, 3, 4]",
            "j": 5
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]",
            "j": 2
        },
        "expected": "#[1, 2, 60, 4, 5]",
        "unexpected": [
            "#[1, 2, 3, 4, 5]",
            "#[1, 60, 3, 4, 5]"
        ]
    },
    {
        "input": {
            "a": "#[60, 30, 20]",
            "j": 1
        },
        "expected": "#[60, 60, 20]",
        "unexpected": [
            "#[60, 30, 20]",
            "#[60, 30, 60]"
        ]
    },
    {
        "input": {
            "a": "#[10, 20, 30]",
            "j": 0
        },
        "expected": "#[60, 20, 30]",
        "unexpected": [
            "#[10, 20, 30]",
            "#[10, 60, 30]"
        ]
    },
    {
        "input": {
            "a": "#[5, 10, 15]",
            "j": 2
        },
        "expected": "#[5, 10, 60]",
        "unexpected": [
            "#[5, 10, 15]",
            "#[5, 60, 15]"
        ]
    },
    {
        "input": {
            "a": "#[0]",
            "j": 0
        },
        "expected": "#[60]",
        "unexpected": [
            "#[0]",
            "#[70]"
        ]
    }
]
-/