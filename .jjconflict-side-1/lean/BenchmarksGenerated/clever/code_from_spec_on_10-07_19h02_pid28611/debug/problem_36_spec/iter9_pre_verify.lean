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
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  (n = 0 → result = 0) ∧
  (0 < n → result = implementation (n - 1) →
    (n % 11 ≠  0 ∧  n % 13 ≠  0) ∨ n.repr.count '7' = 0) ∧
  (0 < n → result ≠ implementation (n - 1) →
    (n % 11 = 0 ∨  n % 13 = 0) ∧
    result - implementation (n - 1) = n.repr.count '7')
-- program termination
∃ result, implementation n = result ∧
spec result

def implementation (n: Nat) : Nat :=
  if n = 0 then 0
  else
    let prev := implementation (n - 1)
    if (n % 11 = 0 ∨ n % 13 = 0) ∧ n.repr.count '7' > 0 then
      prev + n.repr.count '7'
    else
      prev
termination_by n

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  rw [implementation]
  rfl

-- LLM HELPER  
lemma implementation_pos (n : Nat) (h : 0 < n) : 
  implementation n = 
  let prev := implementation (n - 1)
  if (n % 11 = 0 ∨ n % 13 = 0) ∧ n.repr.count '7' > 0 then
    prev + n.repr.count '7'
  else
    prev := by
  rw [implementation]
  rw [if_neg (ne_of_gt h)]

-- LLM HELPER
lemma nat_add_sub_cancel_left (a b : Nat) : a + b - a = b := by
  rw [Nat.add_sub_cancel]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  rw [problem_spec]
  use implementation n
  constructor
  · rfl
  · constructor
    · intro h
      rw [h]
      exact implementation_zero
    · constructor
      · intro h_pos h_eq
        by_cases h_cond : (n % 11 = 0 ∨ n % 13 = 0) ∧ n.repr.count '7' > 0
        · have this : implementation n = implementation (n - 1) + n.repr.count '7' := by
            rw [implementation_pos n h_pos]
            rw [if_pos h_cond]
          rw [this] at h_eq
          exfalso
          have : n.repr.count '7' > 0 := h_cond.2
          linarith
        · have this : implementation n = implementation (n - 1) := by
            rw [implementation_pos n h_pos]
            rw [if_neg h_cond]
          rw [this] at h_eq
          push_neg at h_cond
          cases' Classical.em (n % 11 = 0 ∨ n % 13 = 0) with h_div h_not_div
          · have : n.repr.count '7' = 0 := by
              by_contra h_nonzero
              have : n.repr.count '7' > 0 := Nat.pos_of_ne_zero h_nonzero
              have : (n % 11 = 0 ∨ n % 13 = 0) ∧ n.repr.count '7' > 0 := ⟨h_div, this⟩
              exact h_cond this
            right
            exact this
          · left
            push_neg at h_not_div
            exact h_not_div
      · intro h_pos h_neq
        by_cases h_cond : (n % 11 = 0 ∨ n % 13 = 0) ∧ n.repr.count '7' > 0
        · constructor
          · exact h_cond.1
          · have this : implementation n = implementation (n - 1) + n.repr.count '7' := by
              rw [implementation_pos n h_pos]
              rw [if_pos h_cond]
            rw [this]
            exact nat_add_sub_cancel_left (implementation (n - 1)) (n.repr.count '7')
        · have this : implementation n = implementation (n - 1) := by
            rw [implementation_pos n h_pos]
            rw [if_neg h_cond]
          rw [this] at h_neq
          exfalso
          exact h_neq rfl