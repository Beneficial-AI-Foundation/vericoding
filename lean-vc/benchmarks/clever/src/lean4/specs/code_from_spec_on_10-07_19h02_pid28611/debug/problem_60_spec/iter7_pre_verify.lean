import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n : Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (result = 1 ↔ n = 1) ∧
  (∀ i, implementation (i + 1) - (implementation i) = i + 1)
-- program termination
∃ result, implementation n = result ∧
spec result

def implementation (n: Nat) : Nat := n * (n + 1) / 2

-- LLM HELPER
lemma triangular_formula (n : Nat) : implementation n = n * (n + 1) / 2 := by
  rfl

-- LLM HELPER
lemma triangular_diff (i : Nat) : implementation (i + 1) - implementation i = i + 1 := by
  unfold implementation
  have h1 : (i + 1) * (i + 2) = i * (i + 1) + 2 * (i + 1) := by ring
  rw [h1]
  rw [Nat.add_mul_div_left]
  · ring_nf
    rw [Nat.mul_div_cancel_left]
    norm_num
  · norm_num

-- LLM HELPER
lemma implementation_one : implementation 1 = 1 := by
  unfold implementation
  norm_num

-- LLM HELPER
lemma implementation_ne_one_when_n_ne_one (n : Nat) (h : n ≠ 1) (hn : 0 < n) : implementation n ≠ 1 := by
  unfold implementation
  cases' n with n
  · contradiction
  · cases' n with n
    · contradiction
    · have h1 : n + 2 ≥ 2 := by linarith
      have h2 : n + 3 ≥ 3 := by linarith
      have h3 : (n + 2) * (n + 3) ≥ 6 := by
        have : 2 * 3 ≤ (n + 2) * (n + 3) := Nat.mul_le_mul h1 h2
        linarith
      have h4 : (n + 2) * (n + 3) / 2 ≥ 3 := by
        have : 6 ≤ (n + 2) * (n + 3) := by linarith [h3]
        have : 6 / 2 ≤ (n + 2) * (n + 3) / 2 := Nat.div_le_div_right this
        norm_num at this
        exact this
      intro h_eq
      have : (n + 2) * (n + 3) / 2 = 1 := h_eq
      linarith [h4, this]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · intro h
    constructor
    · constructor
      · intro h_eq
        by_contra h_ne
        have : implementation n ≠ 1 := implementation_ne_one_when_n_ne_one n h_ne h
        contradiction
      · intro h_eq
        rw [h_eq]
        exact implementation_one
    · exact triangular_diff