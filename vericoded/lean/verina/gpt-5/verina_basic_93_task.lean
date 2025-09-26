import Mathlib
-- <vc-preamble>
@[reducible, simp]
def SwapBitvectors_precond (X : UInt8) (Y : UInt8) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def SwapBitvectors (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) : UInt8 × UInt8 :=
  (Y, X)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def SwapBitvectors_postcond (X : UInt8) (Y : UInt8) (result: UInt8 × UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :=
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

theorem SwapBitvectors_spec_satisfied (X: UInt8) (Y: UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :
    SwapBitvectors_postcond (X) (Y) (SwapBitvectors (X) (Y) h_precond) h_precond := by
  constructor
  · simp [SwapBitvectors]
  · constructor
    · simp [SwapBitvectors]
    · intro hne
      constructor
      · simpa [SwapBitvectors] using (fun h : Y = X => hne h.symm)
      · simpa [SwapBitvectors] using hne
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "X": 0,
            "Y": 0
        },
        "expected": "(0, 0)",
        "unexpected": [
            "(0, 1)",
            "(1, 0)"
        ]
    },
    {
        "input": {
            "X": 5,
            "Y": 10
        },
        "expected": "(10, 5)",
        "unexpected": [
            "(5, 10)",
            "(10, 10)",
            "(5, 5)"
        ]
    },
    {
        "input": {
            "X": 255,
            "Y": 1
        },
        "expected": "(1, 255)",
        "unexpected": [
            "(255, 1)",
            "(1, 254)",
            "(0, 255)"
        ]
    },
    {
        "input": {
            "X": 128,
            "Y": 64
        },
        "expected": "(64, 128)",
        "unexpected": [
            "(128, 64)",
            "(64, 64)",
            "(0, 128)"
        ]
    },
    {
        "input": {
            "X": 15,
            "Y": 15
        },
        "expected": "(15, 15)",
        "unexpected": [
            "(15, 16)",
            "(16, 15)",
            "(14, 15)"
        ]
    }
]
-/