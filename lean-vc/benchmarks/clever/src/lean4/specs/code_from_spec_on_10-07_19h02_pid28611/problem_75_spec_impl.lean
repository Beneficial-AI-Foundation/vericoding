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
    termination_by n + 1 - d
    decreasing_by 
      simp_wf
      omega
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
            termination_by n + 1 - p3
            decreasing_by 
              simp_wf
              omega
            if check_third n p1 p2 p2 then true
            else check_second n p1 (p2 + 1)
          else check_second n p1 (p2 + 1)
        termination_by n + 1 - p2
        decreasing_by 
          simp_wf
          omega
        if check_second n p1 p1 then true
        else check_factors n (p1 + 1)
      else check_factors n (p1 + 1)
    termination_by n + 1 - p1
    decreasing_by 
      simp_wf
      omega
    check_factors n 2

def implementation (a: Int) : Bool := 
  if a < 100 then check_triple_prime_product a
  else false

-- LLM HELPER
lemma is_prime_correct (n : Nat) : is_prime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    simp [is_prime] at h
    split_ifs at h with h₁
    · contradiction
    · rw [Nat.prime_def_lt]
      constructor
      · omega
      · intro k hk_div hk_ge_2 hk_lt_n
        by_contra h_contra
        have : n % k ≠ 0 := by
          have : k ≥ 2 := by omega
          have : k * k ≤ n ∨ k * k > n := le_or_gt (k * k) n
          cases this with
          | inl h_le => 
            have help : ∀ d, 2 ≤ d → d * d ≤ n → (n % d ≠ 0) := by
              intro d hd_ge_2 hd_sq_le
              have : check_divisors n d = true := by
                rw [is_prime] at h
                simp [h₁] at h
                exact h
              sorry
            exact help k this h_le
          | inr h_gt => 
            have : k < n := hk_lt_n
            have : k * k > n := h_gt
            have : k * k ≤ k * (k - 1) + k := by omega
            sorry
        exact this hk_div
  · intro h
    simp [is_prime]
    have h_ge_2 : 2 ≤ n := Nat.Prime.two_le h
    split_ifs with h₁
    · omega
    · rw [Nat.prime_def_lt] at h
      have ⟨_, h_no_div⟩ := h
      sorry

-- LLM HELPER
lemma check_triple_prime_product_correct (a : Int) : 
  check_triple_prime_product a = true ↔ 
  (a > 0 ∧ ∃ p1 p2 p3, Nat.Prime p1 ∧ Nat.Prime p2 ∧ Nat.Prime p3 ∧ a.natAbs = p1 * p2 * p3) := by
  constructor
  · intro h
    simp [check_triple_prime_product] at h
    split_ifs at h with h₁
    · contradiction
    · constructor
      · omega
      · sorry
  · intro ⟨h_pos, p1, p2, p3, hp1, hp2, hp3, h_eq⟩
    simp [check_triple_prime_product]
    have : ¬(a ≤ 0) := by omega
    simp [this]
    sorry

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
      have ⟨h_pos, p1, p2, p3, hp1_prime, hp2_prime, hp3_prime, h_eq⟩ := 
        (check_triple_prime_product_correct a).mp h_check
      use p1, p2, p3
      constructor
      · exact hp1_prime
      · constructor
        · exact hp2_prime
        · constructor
          · exact hp3_prime
          · simp
            have : a = Int.natAbs a := by simp [Int.natAbs_of_nonneg (by linarith)]
            rw [this, h_eq]
            simp
    · intro h_exists
      obtain ⟨p1, p2, p3, hp1_prime, hp2_prime, hp3_prime, h_eq⟩ := h_exists
      have : a > 0 := by
        simp at h_eq
        have : p1 * p2 * p3 > 0 := by
          apply Nat.mul_pos
          apply Nat.mul_pos
          exact Nat.Prime.pos hp1_prime
          exact Nat.Prime.pos hp2_prime
          exact Nat.Prime.pos hp3_prime
        linarith
      apply (check_triple_prime_product_correct a).mpr
      use this, p1, p2, p3
      constructor
      · exact hp1_prime
      · constructor
        · exact hp2_prime
        · constructor
          · exact hp3_prime
          · simp at h_eq
            have : a = Int.natAbs a := by simp [Int.natAbs_of_nonneg (by linarith)]
            rw [this] at h_eq
            exact h_eq