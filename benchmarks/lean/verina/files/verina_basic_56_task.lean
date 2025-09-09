@[reducible, simp]
def copy_precond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  src.size ≥ sStart + len ∧
  dest.size ≥ dStart + len

-- <vc-helpers>
def updateSegment : Array Int → Array Int → Nat → Nat → Nat → Array Int
  | r, src, sStart, dStart, 0 => r
  | r, src, sStart, dStart, n+1 =>
      let rNew := r.set! (dStart + n) (src[sStart + n]!)
      updateSegment rNew src sStart dStart n
-- </vc-helpers>

def copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) : Array Int :=
  sorry

@[reducible, simp]
def copy_postcond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result: Array Int) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :=
  result.size = dest.size ∧
  (∀ i, i < dStart → result[i]! = dest[i]!) ∧
  (∀ i, dStart + len ≤ i → i < result.size → result[i]! = dest[i]!) ∧
  (∀ i, i < len → result[dStart + i]! = src[sStart + i]!)

theorem copy_spec_satisfied (src: Array Int) (sStart: Nat) (dest: Array Int) (dStart: Nat) (len: Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :
    copy_postcond (src) (sStart) (dest) (dStart) (len) (copy (src) (sStart) (dest) (dStart) (len) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "src": "#[10, 20, 30]",
            "sStart": 1,
            "dest": "#[1, 2, 3, 4]",
            "dStart": 2,
            "len": 3
        }
    }
]
-- Tests
[
    {
        "input": {
            "src": "#[10, 20, 30, 40, 50]",
            "sStart": 1,
            "dest": "#[1, 2, 3, 4, 5, 6]",
            "dStart": 3,
            "len": 2
        },
        "expected": "#[1, 2, 3, 20, 30, 6]",
        "unexpected": [
            "#[1, 2, 3, 10, 30, 6]",
            "#[1, 2, 3, 20, 40, 6]",
            "#[1, 2, 20, 30, 6, 0]"
        ]
    },
    {
        "input": {
            "src": "#[5, 6, 7, 8]",
            "sStart": 0,
            "dest": "#[9, 9, 9, 9, 9]",
            "dStart": 1,
            "len": 3
        },
        "expected": "#[9, 5, 6, 7, 9]",
        "unexpected": [
            "#[9, 9, 5, 7, 9]",
            "#[9, 5, 7, 6, 9]",
            "#[9, 5, 6, 9, 9]"
        ]
    },
    {
        "input": {
            "src": "#[100, 200]",
            "sStart": 0,
            "dest": "#[1, 2, 3]",
            "dStart": 1,
            "len": 0
        },
        "expected": "#[1, 2, 3]",
        "unexpected": [
            "#[1, 0, 3]",
            "#[0, 2, 3]",
            "#[1, 2, 0]"
        ]
    },
    {
        "input": {
            "src": "#[10, 20, 30, 40, 50]",
            "sStart": 0,
            "dest": "#[0, 0, 0, 0, 0]",
            "dStart": 0,
            "len": 5
        },
        "expected": "#[10, 20, 30, 40, 50]",
        "unexpected": [
            "#[10, 20, 30, 40, 60]",
            "#[0, 20, 30, 40, 50]",
            "#[10, 20, 30, 40, 0]"
        ]
    },
    {
        "input": {
            "src": "#[7, 8, 9, 10]",
            "sStart": 2,
            "dest": "#[1, 2, 3, 4, 5, 6]",
            "dStart": 4,
            "len": 2
        },
        "expected": "#[1, 2, 3, 4, 9, 10]",
        "unexpected": [
            "#[1, 2, 3, 9, 4, 10]",
            "#[1, 2, 9, 4, 3, 10]",
            "#[1, 2, 3, 4, 10, 9]"
        ]
    }
]
-/