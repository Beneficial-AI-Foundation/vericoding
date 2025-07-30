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
    termination_by n - i
    checkDivisors n 2

-- LLM HELPER
lemma isPrime_correct (n: Nat) : isPrime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    simp [isPrime] at h
    split_ifs at h with h1
    · simp at h
    · have : n ≥ 2 := Nat.not_lt.mp h1
      apply Nat.prime_def_lt.mpr
      constructor
      · exact this
      · intro m hm hdiv
        by_contra h_contra
        have : ¬(m = 1) := h_contra
        have : m ≥ 2 := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (Nat.ne_of_gt hm))
        sorry -- This would require a more complex proof about the loop invariant
  · intro h
    simp [isPrime]
    split_ifs with h1
    · have : n < 2 := h1
      have : n ≥ 2 := Nat.Prime.two_le h
      omega
    · sorry -- This would require proving the algorithm is correct

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
        split_ifs at h with h1
        · exact h
        · push_neg at h1
          simp at h1
          cases h1 with
          | inl h1 => 
            have : n ≤ 1 := Int.not_lt.mp h1
            have : n.toNat = 0 ∨ n.toNat = 1 := by
              cases' Int.le_iff_coe_nat_le.mp (le_of_lt (Int.lt_of_le_of_lt this (by norm_num : (1 : Int) < 2))) with k hk
              · simp [Int.toNat, hk]
                by_cases h : n = 0
                · left; simp [h]
                · right
                  have : n = 1 := by omega
                  simp [this]
            cases this with
            | inl h0 => 
              simp [h0]
              exact Nat.not_prime_zero
            | inr h1_case =>
              simp [h1_case]
              exact Nat.not_prime_one
          | inr h2 =>
            have : ¬Nat.Prime n.toNat := by
              rw [← Bool.not_eq_true]
              exact h2
            exact this
      · intro h_prime
        split_ifs with h1
        · rfl
        · push_neg at h1
          simp at h1
          cases h1 with
          | inl h1 =>
            have : n ≤ 1 := Int.not_lt.mp h1
            have : n.toNat ≤ 1 := by
              cases' Int.le_iff_coe_nat_le.mp (le_of_lt (Int.lt_of_le_of_lt this (by norm_num : (1 : Int) < 2))) with k hk
              simp [Int.toNat, hk]
              by_cases h : n = 0
              · simp [h]
              · have : n = 1 := by omega
                simp [this]
            have : ¬Nat.Prime n.toNat := by
              cases' Nat.le_iff_lt_or_eq.mp this with
              | inl h0 => 
                have : n.toNat = 0 := Nat.eq_zero_of_lt_one h0
                simp [h0]
                exact Nat.not_prime_zero
              | inr h1_case =>
                simp [h1_case]
                exact Nat.not_prime_one
            exact absurd h_prime this
          | inr h2 =>
            have : ¬Nat.Prime n.toNat := by
              rw [← Bool.not_eq_true]
              exact h2
            exact absurd h_prime this
    · constructor
      · intro h
        split_ifs at h with h1
        · push_neg at h1
          simp at h1
          have : n > 1 := h1.1
          have : isPrime n.toNat = true := h1.2
          have : Nat.Prime n.toNat := (isPrime_correct n.toNat).mp this
          exact absurd this (Or.elim h (fun h => h) (fun h => by
            have : n ≤ 1 := h
            have : n.toNat ≤ 1 := by
              cases' Int.le_iff_coe_nat_le.mp (le_of_lt (Int.lt_of_le_of_lt this (by norm_num : (1 : Int) < 2))) with k hk
              simp [Int.toNat, hk]
              by_cases h_case : n = 0
              · simp [h_case]
              · have : n = 1 := by omega
                simp [this]
            have : ¬Nat.Prime n.toNat := by
              cases' Nat.le_iff_lt_or_eq.mp this with
              | inl h0 => 
                have : n.toNat = 0 := Nat.eq_zero_of_lt_one h0
                simp [h0]
                exact Nat.not_prime_zero
              | inr h1_case =>
                simp [h1_case]
                exact Nat.not_prime_one
            exact this))
        · exact h
      · intro h
        split_ifs with h1
        · push_neg at h1
          simp at h1
          have : n > 1 := h1.1
          have : isPrime n.toNat = true := h1.2
          have : Nat.Prime n.toNat := (isPrime_correct n.toNat).mp this
          cases h with
          | inl h_not_prime => exact absurd h_not_prime (not_not.mpr this)
          | inr h_le => 
            have : n ≤ 1 := h_le
            omega
        · rfl