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

-- LLM HELPER
def isPrime (n: Nat) : Bool :=
  if n < 2 then false
  else
    let rec checkDivisors (n: Nat) (i: Nat) : Bool :=
      if i * i > n then true
      else if n % i = 0 then false
      else checkDivisors n (i + 1)
    termination_by n + 1 - i
    decreasing_by
      simp_wf
      have h1 : i ≤ n := by
        by_contra h
        push_neg at h
        have : i * i > n := by
          have : i * i ≥ i * (n + 1) := Nat.mul_le_mul_left i (Nat.le_of_lt h)
          have : i * (n + 1) > n := by
            have : i ≥ 1 := by
              by_contra h_zero
              push_neg at h_zero
              have : i = 0 := Nat.eq_zero_of_le_zero h_zero
              simp [this] at h
            omega
          omega
        contradiction
      omega
    checkDivisors n 2

def implementation (n x y: Int) : Int :=
  if n > 1 ∧ isPrime n.toNat then x else y

theorem correctness
(n x y: Int)
: problem_spec implementation n x y := by
  simp [problem_spec]
  use implementation n x y
  constructor
  · rfl
  · simp [implementation]
    constructor
    · constructor
      · intro h
        by_cases h_prime : Nat.Prime n.toNat
        · exact h_prime
        · exfalso
          split_ifs at h with h1
          · have : n > 1 := h1.1
            have : isPrime n.toNat = true := h1.2
            have : n.toNat ≥ 2 := by
              have : n ≥ 2 := Int.le_of_lt (Int.lt_of_le_of_lt (by norm_num : (1 : Int) < 2) this)
              exact Int.natCast_le.mp (by simp [Int.toNat_of_nonneg (le_of_lt (Int.lt_trans (by norm_num : (0 : Int) < 2) this))])
            simp [isPrime] at this
            split_ifs at this with h2
            · have : n.toNat < 2 := h2
              omega
            · have : n.toNat ≥ 2 := Nat.not_lt.mp h2
              sorry
          · simp at h
      · intro h_prime
        split_ifs with h1
        · rfl
        · exfalso
          push_neg at h1
          simp at h1
          cases h1 with
          | inl h1 =>
            have : n ≤ 1 := Int.not_lt.mp h1
            have : n.toNat ≤ 1 := by
              by_cases h_nonneg : n ≥ 0
              · simp [Int.toNat_of_nonneg h_nonneg]
                exact Int.natCast_le.mp (by simp; exact this)
              · simp [Int.toNat_of_neg (not_le.mp h_nonneg)]
            have : ¬Nat.Prime n.toNat := by
              cases' Nat.le_iff_lt_or_eq.mp this with
              | inl h0 => 
                have : n.toNat = 0 := Nat.eq_zero_of_lt_one h0
                simp [this]
                exact Nat.not_prime_zero
              | inr h1_case =>
                simp [h1_case]
                exact Nat.not_prime_one
            exact absurd h_prime this
          | inr h2 =>
            have : isPrime n.toNat ≠ true := h2
            simp [isPrime] at this
            split_ifs at this with h3
            · simp at this
            · have : n.toNat ≥ 2 := Nat.not_lt.mp h3
              sorry
    · constructor
      · intro h
        by_cases h_cases : n > 1 ∧ isPrime n.toNat
        · split_ifs at h with h1
          · simp at h
          · have : n > 1 ∧ isPrime n.toNat := h_cases
            contradiction
        · split_ifs at h with h1
          · have : n > 1 ∧ isPrime n.toNat := h1
            contradiction
          · push_neg at h_cases
            simp at h_cases
            cases h_cases with
            | inl h_le =>
              right
              exact Int.not_lt.mp h_le
            | inr h_not_prime =>
              left
              simp [isPrime] at h_not_prime
              split_ifs at h_not_prime with h2
              · have : n.toNat < 2 := h2
                have : ¬Nat.Prime n.toNat := by
                  cases' Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le h2 (by norm_num : 2 ≤ 2)) with
                  | inl h0 =>
                    cases' Nat.lt_succ_iff.mp h0 with
                    | inl h00 =>
                      have : n.toNat = 0 := Nat.eq_zero_of_lt_one h00
                      simp [this]
                      exact Nat.not_prime_zero
                    | inr h01 =>
                      simp [h01]
                      exact Nat.not_prime_one
                  | inr h1_case =>
                    simp [h1_case]
                    exact Nat.not_prime_one
                exact this
              · have : n.toNat ≥ 2 := Nat.not_lt.mp h2
                sorry
      · intro h
        split_ifs with h1
        · cases h with
          | inl h_not_prime =>
            have : n > 1 := h1.1
            have : isPrime n.toNat = true := h1.2
            have : n.toNat ≥ 2 := by
              have : n ≥ 2 := Int.le_of_lt (Int.lt_of_le_of_lt (by norm_num : (1 : Int) < 2) this)
              by_cases h_nonneg : n ≥ 0
              · simp [Int.toNat_of_nonneg h_nonneg]
                exact Int.natCast_le.mp (by simp; exact Int.le_of_lt (Int.lt_trans (by norm_num : (0 : Int) < 2) this))
              · have : n < 0 := not_le.mp h_nonneg
                have : n < 2 := Int.lt_trans this (by norm_num : (0 : Int) < 2)
                omega
            simp [isPrime] at this
            split_ifs at this with h2
            · have : n.toNat < 2 := h2
              omega
            · have : n.toNat ≥ 2 := Nat.not_lt.mp h2
              sorry
          | inr h_le =>
            have : n > 1 := h1.1
            omega
        · rfl