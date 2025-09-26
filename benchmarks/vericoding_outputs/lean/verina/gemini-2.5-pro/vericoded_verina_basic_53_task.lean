import Mathlib
-- <vc-preamble>
@[reducible, simp]
def CalSum_precond (N : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- A recursive function to calculate the sum of natural numbers up to n.
def sum_rec : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sum_rec n

-- LLM HELPER
-- A proof that 2 * sum_rec n = n * (n + 1), known as Gauss's summation formula.
-- We prove it by induction on n.
theorem sum_rec_closed_form (n : Nat) : 2 * sum_rec n = n * (n + 1) := by
  induction n with
  | zero =>
    simp [sum_rec]
  | succ n ih =>
    rw [sum_rec, Nat.left_distrib, ih]
    ring

-- </vc-helpers>

-- <vc-definitions>
def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  sum_rec N
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  2 * result = N * (N + 1)

theorem CalSum_spec_satisfied (N: Nat) (h_precond : CalSum_precond (N)) :
    CalSum_postcond (N) (CalSum (N) h_precond) h_precond := by
  rw [CalSum_postcond, CalSum]
  exact sum_rec_closed_form N
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "N": 0
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
            "N": 1
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            3
        ]
    },
    {
        "input": {
            "N": 5
        },
        "expected": 15,
        "unexpected": [
            10,
            16,
            20
        ]
    },
    {
        "input": {
            "N": 10
        },
        "expected": 55,
        "unexpected": [
            54,
            56,
            50
        ]
    },
    {
        "input": {
            "N": 20
        },
        "expected": 210,
        "unexpected": [
            200,
            220,
            205
        ]
    }
]
-/