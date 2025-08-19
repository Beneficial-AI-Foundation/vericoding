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

-- LLM HELPER
def count_sevens (n : Nat) : Nat := n.repr.count '7'

-- LLM HELPER
def should_add_sevens (n : Nat) : Bool := (n % 11 = 0) || (n % 13 = 0)

def implementation (n: Nat) : Nat := 
  if n = 0 then 0
  else 
    let prev := implementation (n - 1)
    if should_add_sevens n then
      prev + count_sevens n
    else
      prev

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_pos (n : Nat) (h : 0 < n) : 
  implementation n = 
    if should_add_sevens n then
      implementation (n - 1) + count_sevens n
    else
      implementation (n - 1) := by
  simp [implementation]
  rw [if_neg (Ne.symm (ne_of_gt h))]

-- LLM HELPER
lemma should_add_sevens_iff (n : Nat) : 
  should_add_sevens n = true ↔ (n % 11 = 0 ∨ n % 13 = 0) := by
  simp [should_add_sevens, Bool.or_eq_true]

-- LLM HELPER
lemma should_add_sevens_false_iff (n : Nat) : 
  should_add_sevens n = false ↔ (n % 11 ≠ 0 ∧ n % 13 ≠ 0) := by
  simp [should_add_sevens, Bool.or_eq_false]

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · simp only [count_sevens]
    constructor
    · intro h
      rw [implementation_zero]
    · constructor
      · intro h_pos h_eq
        rw [implementation_pos n h_pos] at h_eq
        by_cases h_should : should_add_sevens n
        · simp [h_should] at h_eq
          exfalso
          have : count_sevens n = 0 := by
            have : implementation n = implementation (n - 1) + count_sevens n := by
              rw [implementation_pos n h_pos, if_pos h_should]
            rw [this] at h_eq
            simp at h_eq
          right
          exact this
        · simp [h_should] at h_eq
          left
          rw [should_add_sevens_false_iff] at h_should
          exact h_should
      · intro h_pos h_neq
        rw [implementation_pos n h_pos] at h_neq
        by_cases h_should : should_add_sevens n
        · simp [h_should] at h_neq
          constructor
          · rw [should_add_sevens_iff] at h_should
            exact h_should
          · rw [implementation_pos n h_pos, if_pos h_should]
            simp
        · simp [h_should] at h_neq
          exfalso
          exact h_neq rfl