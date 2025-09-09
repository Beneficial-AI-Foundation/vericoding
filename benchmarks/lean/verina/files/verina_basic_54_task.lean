@[reducible, simp]
def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList

-- <vc-helpers>
def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n
-- </vc-helpers>

def CanyonSearch (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) : Nat :=
  sorry

@[reducible, simp]
def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) (h_precond : CanyonSearch_precond (a) (b)) :=
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))

theorem CanyonSearch_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : CanyonSearch_precond (a) (b)) :
    CanyonSearch_postcond (a) (b) (CanyonSearch (a) (b) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[]",
            "b": "#[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[1, 3, 5]",
            "b": "#[2, 4, 6]"
        },
        "expected": "1",
        "unexpected": [
            "0",
            "2",
            "3"
        ]
    },
    {
        "input": {
            "a": "#[-5, -2, 0]",
            "b": "#[1, 3]"
        },
        "expected": "1",
        "unexpected": [
            "0",
            "2",
            "5"
        ]
    },
    {
        "input": {
            "a": "#[10, 20, 30]",
            "b": "#[5, 15, 25]"
        },
        "expected": "5",
        "unexpected": [
            "3",
            "7",
            "10"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]",
            "b": "#[3]"
        },
        "expected": "0",
        "unexpected": [
            "1",
            "2",
            "3"
        ]
    },
    {
        "input": {
            "a": "#[-10, -5, 0, 5, 10]",
            "b": "#[-3, 2, 8]"
        },
        "expected": "2",
        "unexpected": [
            "1",
            "3",
            "4"
        ]
    }
]
-/