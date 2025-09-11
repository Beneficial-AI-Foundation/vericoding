-- <vc-preamble>
@[reducible, simp]
def remove_front_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc
-- </vc-helpers>

-- <vc-definitions>
def remove_front (a : Array Int) (h_precond : remove_front_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def remove_front_postcond (a : Array Int) (result: Array Int) (h_precond : remove_front_precond (a)) :=
  a.size > 0 ∧ result.size = a.size - 1 ∧ (∀ i : Nat, i < result.size → result[i]! = a[i + 1]!)

theorem remove_front_spec_satisfied (a: Array Int) (h_precond : remove_front_precond (a)) :
    remove_front_postcond (a) (remove_front (a) h_precond) h_precond := by
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
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": "#[2, 3, 4, 5]",
        "unexpected": [
            "#[1, 2, 3, 4, 5]",
            "#[3, 4, 5]",
            "#[2, 3, 4]"
        ]
    },
    {
        "input": {
            "a": "#[10, 20, 30]"
        },
        "expected": "#[20, 30]",
        "unexpected": [
            "#[10, 20, 30]",
            "#[10, 30]",
            "#[10, 20]"
        ]
    },
    {
        "input": {
            "a": "#[0, -1, -2, -3]"
        },
        "expected": "#[-1, -2, -3]",
        "unexpected": [
            "#[0, -1, -2, -3]",
            "#[-1, -3]",
            "#[-2, -3]"
        ]
    },
    {
        "input": {
            "a": "#[7]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[7]",
            "#[0]",
            "#[7, 7]"
        ]
    },
    {
        "input": {
            "a": "#[100, 0, 50]"
        },
        "expected": "#[0, 50]",
        "unexpected": [
            "#[100, 0, 50]",
            "#[50]",
            "#[0]"
        ]
    }
]
-/