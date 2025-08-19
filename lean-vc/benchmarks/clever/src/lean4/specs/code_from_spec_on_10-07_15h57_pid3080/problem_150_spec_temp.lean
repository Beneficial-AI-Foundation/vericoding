import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
lemma prime_positive (n : ℕ) (h : Nat.Prime n) : n > 1 := by
  exact Nat.Prime.one_lt h

-- LLM HELPER
lemma int_toNat_pos (n : Int) (h : n > 1) : n.toNat > 1 := by
  rw [Int.toNat_of_nonneg (le_of_lt (Int.zero_lt_one.trans h))]
  exact Int.coe_nat_lt_coe_nat_iff.mp h

-- LLM HELPER
lemma not_prime_or_le_one_of_not_both (n : Int) (h : ¬(n > 1 ∧ Nat.Prime n.toNat)) : 
  ¬ Nat.Prime n.toNat ∨ n ≤ 1 := by
  push_neg at h
  cases h with
  | inl h_not_gt => right; exact h_not_gt
  | inr h_not_prime => left; exact h_not_prime

-- LLM HELPER
lemma prime_implies_gt_one (n : Int) (h : Nat.Prime n.toNat) : n > 1 := by
  have h_pos : n.toNat > 1 := Nat.Prime.one_lt h
  cases' Int.toNat_eq_max n 0 with h_eq h_eq
  · rw [h_eq] at h_pos
    exact Int.coe_nat_lt_coe_nat_iff.mpr h_pos
  · rw [h_eq] at h_pos
    simp at h_pos

theorem correctness
(n x y: Int)
: problem_spec implementation n x y := by
  unfold problem_spec
  simp [implementation]
  by_cases h : n > 1 ∧ Nat.Prime n.toNat
  · -- Case: n > 1 and n.toNat is prime
    simp [h]
    use x
    constructor
    · rfl
    · constructor
      · constructor
        · intro h_eq
          exact h.2
        · intro h_prime
          rfl
      · constructor
        · intro h_eq
          rw [h_eq]
          left
          exact h.2
        · intro h_not_prime_or_le
          cases h_not_prime_or_le with
          | inl h_not_prime => exact absurd h.2 h_not_prime
          | inr h_le => exact absurd h.1 (not_lt.mpr h_le)
  · -- Case: ¬(n > 1 ∧ Nat.Prime n.toNat)
    simp [h]
    use y
    constructor
    · rfl
    · constructor
      · constructor
        · intro h_eq
          rw [h_eq]
          push_neg at h
          cases h with
          | inl h_not_gt => 
            intro h_prime
            exact absurd (prime_implies_gt_one n h_prime) h_not_gt
          | inr h_not_prime => exact h_not_prime
        · intro h_prime
          have : n > 1 ∧ Nat.Prime n.toNat := ⟨prime_implies_gt_one n h_prime, h_prime⟩
          exact absurd this h
      · constructor
        · intro h_eq
          exact not_prime_or_le_one_of_not_both n h
        · intro h_not_prime_or_le
          rfl