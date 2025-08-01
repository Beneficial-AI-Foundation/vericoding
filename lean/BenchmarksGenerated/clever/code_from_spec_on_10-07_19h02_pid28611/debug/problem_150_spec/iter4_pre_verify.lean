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
              have : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_zero)
              simp [this] at h
            omega
          omega
        contradiction
      omega
    checkDivisors n 2

-- LLM HELPER
lemma isPrime_iff_prime (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  simp [isPrime]
  split_ifs with h
  · simp
    constructor
    · intro h_false
      contradiction
    · intro h_prime
      exfalso
      have : n ≥ 2 := Nat.Prime.two_le h_prime
      omega
  · have n_ge_2 : n ≥ 2 := Nat.not_lt.mp h
    constructor
    · intro h_true
      rw [Nat.prime_iff_two_le_and_forall_dvd]
      constructor
      · exact n_ge_2
      · intro m hm
        by_contra h_contra
        push_neg at h_contra
        have : 2 ≤ m := h_contra.1
        have : m < n := h_contra.2
        have : m * m ≤ n := by
          by_contra h_sq
          push_neg at h_sq
          have : m * m > n := h_sq
          have : isPrime n = true := by
            simp [isPrime]
            split_ifs with h_lt
            · exfalso
              omega
            · have : n ≥ 2 := Nat.not_lt.mp h_lt
              apply (checkDivisors n 2).eq_true_of_ne_false
              intro h_false
              have : ∃ i, 2 ≤ i ∧ i * i ≤ n ∧ n % i = 0 := by
                sorry
              obtain ⟨i, hi_ge, hi_sq, hi_div⟩ := this
              have : i < m := by
                by_contra h_not_lt
                push_neg at h_not_lt
                have : m ≤ i := h_not_lt
                have : m * m ≤ i * i := Nat.mul_le_mul' this this
                have : i * i ≤ n := hi_sq
                have : m * m ≤ n := Nat.le_trans this hi_sq
                omega
              have : m ∣ n := hm
              have : i ∣ n := Nat.dvd_of_mod_eq_zero hi_div
              sorry
          exact h_true
        sorry
    · intro h_prime
      apply (checkDivisors n 2).eq_true_of_ne_false
      intro h_false
      have : ∃ i, 2 ≤ i ∧ i * i ≤ n ∧ n % i = 0 := by
        sorry
      obtain ⟨i, hi_ge, hi_sq, hi_div⟩ := this
      have : i ∣ n := Nat.dvd_of_mod_eq_zero hi_div
      have : i = 1 ∨ i = n := Nat.prime_iff_two_le_and_forall_dvd.mp h_prime i this
      cases this with
      | inl h1 =>
        have : i ≥ 2 := hi_ge
        omega
      | inr hn =>
        have : n = i := hn.symm
        have : i * i ≤ n := hi_sq
        rw [this] at hi_sq
        have : i * i ≤ i := hi_sq
        have : i ≤ 1 := by
          by_contra h_gt
          push_neg at h_gt
          have : i ≥ 2 := Nat.succ_le_iff.mpr h_gt
          have : i * i ≥ 2 * 2 := Nat.mul_le_mul' this this
          have : i * i ≥ 4 := by simp at this; exact this
          have : i ≥ 4 := Nat.le_of_mul_le_mul_left this (by norm_num : 0 < i)
          have : i * i ≥ 4 * 4 := Nat.mul_le_mul' this this
          have : i * i ≥ 16 := by simp at this; exact this
          omega
        have : i ≥ 2 := hi_ge
        omega

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
            have : Nat.Prime n.toNat := isPrime_iff_prime n.toNat |>.mp this
            contradiction
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
            have : ¬Nat.Prime n.toNat := by
              rw [←isPrime_iff_prime]
              exact Bool.not_eq_true_iff_eq_false.mp this
            contradiction
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
              rw [←isPrime_iff_prime]
              exact Bool.not_eq_true_iff_eq_false.mp h_not_prime
      · intro h
        split_ifs with h1
        · cases h with
          | inl h_not_prime =>
            have : isPrime n.toNat = true := h1.2
            have : Nat.Prime n.toNat := isPrime_iff_prime n.toNat |>.mp this
            contradiction
          | inr h_le =>
            have : n > 1 := h1.1
            omega
        · rfl