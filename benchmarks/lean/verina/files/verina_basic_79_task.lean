@[reducible, simp]
def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ x < a.size

-- <vc-helpers>
def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1
-- </vc-helpers>

def onlineMax (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
  sorry

@[reducible, simp]
def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)

theorem onlineMax_spec_satisfied (a: Array Int) (x: Nat) (h_precond : onlineMax_precond (a) (x)) :
    onlineMax_postcond (a) (x) (onlineMax (a) (x) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[]",
            "x": 2
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[3, 7, 5, 2, 9]",
            "x": 3
        },
        "expected": "(7, 4)",
        "unexpected": [
            "(7, 3)",
            "(5, 4)"
        ]
    },
    {
        "input": {
            "a": "#[10, 10, 5, 1]",
            "x": 2
        },
        "expected": "(10, 3)",
        "unexpected": [
            "(10, 2)",
            "(7, 3)"
        ]
    },
    {
        "input": {
            "a": "#[1, 3, 3, 3, 1]",
            "x": 2
        },
        "expected": "(3, 4)",
        "unexpected": [
            "(2, 4)",
            "(3, 3)"
        ]
    },
    {
        "input": {
            "a": "#[5, 4, 4, 6, 2]",
            "x": 2
        },
        "expected": "(5, 3)",
        "unexpected": [
            "(4, 2)",
            "(5, 2)",
            "(6, 3)"
        ]
    },
    {
        "input": {
            "a": "#[2, 8, 7, 7, 7]",
            "x": 3
        },
        "expected": "(8, 4)",
        "unexpected": [
            "(7, 4)",
            "(8, 3)"
        ]
    }
]
-/