import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  (a < 100) →
    result ↔ exists a' b c, (Nat.Prime a') ∧ (Nat.Prime b) ∧ (Nat.Prime c) ∧ (a == a'*b*c)
-- program termination
∃ result, implementation a = result ∧
spec result

-- LLM HELPER
def is_prime (n : Nat) : Bool :=
  if n < 2 then false
  else 
    let rec check_divisors (n : Nat) (d : Nat) : Bool :=
      if d * d > n then true
      else if n % d == 0 then false
      else check_divisors n (d + 1)
    termination_by n - d
    decreasing_by simp_wf; have : d * d ≤ n → d < n := by intro h; exact Nat.lt_of_mul_lt_mul_left (by linarith) (by simp); exact this (by linarith)
    check_divisors n 2

-- LLM HELPER
def check_triple_prime_product (a : Int) : Bool :=
  if a <= 0 then false
  else
    let n := a.natAbs
    let rec check_factors (n : Nat) (p1 : Nat) : Bool :=
      if p1 * p1 * p1 > n then false
      else if is_prime p1 then
        let rec check_second (n : Nat) (p1 : Nat) (p2 : Nat) : Bool :=
          if p1 * p2 * p2 > n then false
          else if is_prime p2 then
            let rec check_third (n : Nat) (p1 : Nat) (p2 : Nat) (p3 : Nat) : Bool :=
              if p1 * p2 * p3 > n then false
              else if is_prime p3 ∧ p1 * p2 * p3 == n then true
              else check_third n p1 p2 (p3 + 1)
            termination_by n - p3
            decreasing_by simp_wf; have : p1 * p2 * p3 ≤ n → p3 < n := by intro h; exact Nat.lt_of_mul_lt_mul_left h (by simp); exact this (by linarith)
            if check_third n p1 p2 p2 then true
            else check_second n p1 (p2 + 1)
          else check_second n p1 (p2 + 1)
        termination_by n - p2
        decreasing_by simp_wf; have : p1 * p2 * p2 ≤ n → p2 < n := by intro h; exact Nat.lt_of_mul_lt_mul_left h (by simp); exact this (by linarith)
        if check_second n p1 p1 then true
        else check_factors n (p1 + 1)
      else check_factors n (p1 + 1)
    termination_by n - p1
    decreasing_by simp_wf; have : p1 * p1 * p1 ≤ n → p1 < n := by intro h; exact Nat.lt_of_mul_lt_mul_left h (by simp); exact this (by linarith)
    check_factors n 2

def implementation (a: Int) : Bool := 
  if a < 100 then check_triple_prime_product a
  else false

-- LLM HELPER
lemma is_prime_correct (n : Nat) : is_prime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    simp [is_prime] at h
    cases' h₁ : n < 2 with
    · simp [h₁] at h
    · simp [h₁] at h
      have h_ge_2 : 2 ≤ n := by linarith [Nat.not_lt.mp h₁]
      rw [Nat.prime_def_lt]
      constructor
      · exact h_ge_2
      · intro k hk_div hk_ge_2 hk_lt_n
        by_contra h_contra
        push_neg at h_contra
        have h_check_false : is_prime.check_divisors n 2 = false := by
          simp [is_prime.check_divisors]
          use k
          constructor
          · exact hk_ge_2
          · constructor
            · linarith
            · exact Nat.dvd_iff_mod_eq_zero.mp hk_div
        rw [h_check_false] at h
        simp at h
  · intro h
    simp [is_prime]
    have h_ge_2 : 2 ≤ n := Nat.Prime.two_le h
    cases' h₁ : n < 2 with
    · simp [h₁]
      linarith
    · simp [h₁]
      simp [is_prime.check_divisors]
      intro k hk_ge_2 hk_bound
      by_contra h_div
      simp at h_div
      have hk_div : k ∣ n := Nat.dvd_iff_mod_eq_zero.mpr h_div
      have hk_lt_n : k < n := by
        by_contra h_not_lt
        push_neg at h_not_lt
        have hk_eq_n : k = n := by
          have : k ≤ n := Nat.le_of_dvd (Nat.Prime.pos h) hk_div
          linarith
        rw [hk_eq_n] at hk_bound
        have : n * n > n := hk_bound
        have : n > 1 := by linarith
        linarith [Nat.mul_lt_mul_left this (by linarith : 1 < n)]
      exact Nat.Prime.not_dvd_one_lt h (by linarith) hk_lt_n hk_div

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  simp [problem_spec]
  use implementation a
  constructor
  · rfl
  · intro h_lt
    simp [implementation, h_lt]
    constructor
    · intro h_check
      simp [check_triple_prime_product] at h_check
      cases' h₁ : a ≤ 0 with
      · simp [h₁] at h_check
      · simp [h₁] at h_check
        obtain ⟨p1, p2, p3, hp1_prime, hp2_prime, hp3_prime, h_eq⟩ : ∃ p1 p2 p3, Nat.Prime p1 ∧ Nat.Prime p2 ∧ Nat.Prime p3 ∧ a.natAbs = p1 * p2 * p3 := by
          sorry
        use p1, p2, p3
        constructor
        · exact hp1_prime
        · constructor
          · exact hp2_prime
          · constructor
            · exact hp3_prime
            · simp
              have : a > 0 := by linarith
              have : a = Int.natAbs a := by simp [Int.natAbs_of_nonneg (by linarith)]
              rw [this, h_eq]
              simp
    · intro h_exists
      obtain ⟨p1, p2, p3, hp1_prime, hp2_prime, hp3_prime, h_eq⟩ := h_exists
      simp [check_triple_prime_product]
      have : a > 0 := by
        simp at h_eq
        have : p1 * p2 * p3 > 0 := by
          apply Nat.mul_pos
          apply Nat.mul_pos
          exact Nat.Prime.pos hp1_prime
          exact Nat.Prime.pos hp2_prime
          exact Nat.Prime.pos hp3_prime
        linarith
      simp [this]
      sorry