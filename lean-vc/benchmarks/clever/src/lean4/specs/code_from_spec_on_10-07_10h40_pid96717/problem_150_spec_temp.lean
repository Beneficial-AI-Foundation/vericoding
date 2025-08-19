import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def Nat.Prime (n : Nat) : Prop := n > 1 ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

-- LLM HELPER
lemma Nat.Prime.one_lt {n : Nat} (h : Nat.Prime n) : n > 1 := h.1

def problem_spec
-- function signature
(impl: Int → Int → Int → Int)
-- inputs
(n x y: Int) :=
-- spec
let spec (result: Int) :=
(result = x ↔ Nat.Prime n.toNat) ∧
(result = y ↔ (¬ Nat.Prime n.toNat ∨ n ≤ 1))
-- program terminates
∃ result, impl n x y = result ∧
-- return value satisfies spec
spec result

def implementation (n x y: Int) : Int := 
  if n > 1 ∧ Nat.Prime n.toNat then x else y

-- LLM HELPER
lemma toNat_pos_of_pos {n : Int} (h : n > 1) : n.toNat > 1 := by
  cases' n with n n
  · simp [Int.toNat]
    exact Nat.cast_pos.mp h
  · simp [Int.toNat]
    omega

-- LLM HELPER
lemma not_prime_or_le_one_iff (n : Int) : 
  (¬ Nat.Prime n.toNat ∨ n ≤ 1) ↔ ¬(n > 1 ∧ Nat.Prime n.toNat) := by
  constructor
  · intro h
    cases h with
    | inl h1 => 
      intro ⟨h2, h3⟩
      exact h1 h3
    | inr h1 =>
      intro ⟨h2, h3⟩
      omega
  · intro h
    by_cases h1 : n > 1
    · left
      intro hp
      exact h ⟨h1, hp⟩
    · right
      omega

theorem correctness
(n x y: Int)
: problem_spec implementation n x y := by
  unfold problem_spec implementation
  use if n > 1 ∧ Nat.Prime n.toNat then x else y
  constructor
  · rfl
  · unfold problem_spec
    simp only [ite_eq_left_iff, ite_eq_right_iff]
    constructor
    · constructor
      · intro h
        by_cases h1 : n > 1 ∧ Nat.Prime n.toNat
        · simp [h1]
          exact h1.2
        · simp [h1]
          rw [← h]
          rw [not_prime_or_le_one_iff]
          exact h1
      · intro h
        by_cases h1 : n > 1 ∧ Nat.Prime n.toNat
        · simp [h1]
        · simp [h1]
          exfalso
          exact h1 ⟨by omega [Nat.Prime.one_lt h], h⟩
    · constructor
      · intro h
        by_cases h1 : n > 1 ∧ Nat.Prime n.toNat
        · simp [h1] at h
          rw [← h]
          rw [not_prime_or_le_one_iff]
          exact h1
        · simp [h1]
          rw [not_prime_or_le_one_iff]
          exact h1
      · intro h
        by_cases h1 : n > 1 ∧ Nat.Prime n.toNat
        · simp [h1]
          rw [not_prime_or_le_one_iff] at h
          exact absurd h1 h
        · simp [h1]