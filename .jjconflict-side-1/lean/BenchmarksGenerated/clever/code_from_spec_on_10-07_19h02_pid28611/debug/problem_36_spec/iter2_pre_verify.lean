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
  simp [implementation]

-- LLM HELPER
lemma implementation_pos (n : Nat) (h : 0 < n) : 
  implementation n = 
  let prev := implementation (n - 1)
  if (n % 11 = 0 ∨ n % 13 = 0) ∧ n.repr.count '7' > 0 then
    prev + n.repr.count '7'
  else
    prev := by
  simp [implementation]
  rw [if_neg (ne_of_gt h)]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · constructor
    · intro h
      rw [implementation_zero, h]
    · constructor
      · intro h_pos h_eq
        rw [implementation_pos n h_pos] at h_eq
        simp at h_eq
        split_ifs at h_eq with h_cond
        · exfalso
          simp at h_eq
          have : n.repr.count '7' > 0 := h_cond.2
          linarith
        · simp at h_eq
          push_neg at h_cond
          cases' Classical.em (n % 11 = 0 ∨ n % 13 = 0) with h_div h_not_div
          · have : n.repr.count '7' = 0 := h_cond h_div
            right
            exact this
          · left
            push_neg at h_not_div
            exact h_not_div
      · intro h_pos h_neq
        rw [implementation_pos n h_pos] at h_neq
        simp at h_neq
        split_ifs at h_neq with h_cond
        · constructor
          · exact h_cond.1
          · rw [implementation_pos n h_pos]
            simp
            rw [if_pos h_cond]
            simp
            rw [Nat.add_sub_cancel]
        · exfalso
          simp at h_neq
          exact h_neq