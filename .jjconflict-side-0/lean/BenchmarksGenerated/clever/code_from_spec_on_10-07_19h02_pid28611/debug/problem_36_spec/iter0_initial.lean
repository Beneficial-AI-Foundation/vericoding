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

-- LLM HELPER
lemma nat_sub_one_lt (n : Nat) (h : 0 < n) : n - 1 < n := by
  cases' n with n'
  · contradiction
  · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    exact Nat.lt_succ_self n'

-- LLM HELPER
lemma implementation_unfold (n : Nat) (h : 0 < n) : 
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
  · simp only [and_true]
    constructor
    · intro h
      simp [implementation, if_pos h]
    · constructor
      · intro h_pos h_eq
        rw [implementation_unfold n h_pos] at h_eq
        simp at h_eq
        split_ifs at h_eq with h_cond
        · simp at h_eq
        · simp at h_eq
          cases' h_cond with h_not_div h_no_seven
          · left
            exact h_not_div
          · right
            exact h_no_seven
      · intro h_pos h_neq
        rw [implementation_unfold n h_pos] at h_neq
        simp at h_neq
        split_ifs at h_neq with h_cond
        · simp at h_neq
          constructor
          · exact h_cond.1
          · rw [implementation_unfold n h_pos]
            simp
            rw [if_pos h_cond]
            simp
            exact Nat.add_sub_cancel _ _
        · simp at h_neq