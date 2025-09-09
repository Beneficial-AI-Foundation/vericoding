@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = e

-- <vc-helpers>
def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0
-- </vc-helpers>

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  sorry

@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)

theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]",
            "e": 6
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]",
            "e": 3
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
            "a": "#[10, 20, 30, 40, 50]",
            "e": 10
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
            "a": "#[5, 4, 3, 2, 1]",
            "e": 1
        },
        "expected": 4,
        "unexpected": [
            0,
            1,
            2
        ]
    },
    {
        "input": {
            "a": "#[-1, 0, 1, 2]",
            "e": -1
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
            "a": "#[7, 8, 7, 9, 7]",
            "e": 7
        },
        "expected": 0,
        "unexpected": [
            2,
            3,
            4
        ]
    }
]
-/