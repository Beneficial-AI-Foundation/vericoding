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
    decreasing_by simp_wf; exact Nat.sub_lt_self (by linarith) (by simp)
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
            decreasing_by simp_wf; exact Nat.sub_lt_self (by linarith) (by simp)
            if check_third n p1 p2 p2 then true
            else check_second n p1 (p2 + 1)
          else check_second n p1 (p2 + 1)
        termination_by n - p2
        decreasing_by simp_wf; exact Nat.sub_lt_self (by linarith) (by simp)
        if check_second n p1 p1 then true
        else check_factors n (p1 + 1)
      else check_factors n (p1 + 1)
    termination_by n - p1
    decreasing_by simp_wf; exact Nat.sub_lt_self (by linarith) (by simp)
    check_factors n 2

def implementation (a: Int) : Bool := 
  if a < 100 then check_triple_prime_product a
  else false

-- LLM HELPER
lemma is_prime_correct (n : Nat) : is_prime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    simp [is_prime] at h
    split at h
    · simp at h
    · rename_i h_ge
      simp at h_ge
      have h_ge_2 : 2 ≤ n := by linarith
      apply Nat.prime_def_lt.mpr
      constructor
      · exact h_ge_2
      · intro k hk_div
        have : k = 1 ∨ k = n := by
          by_contra h_contra
          push_neg at h_contra
          have h_k_ge_2 : k ≥ 2 := by
            have : k > 1 := by
              cases' Nat.eq_or_lt_of_le (Nat.one_le_of_lt (Nat.pos_of_dvd_of_pos hk_div (by linarith : 0 < n))) with h_eq h_lt
              · simp at h_contra; exact absurd h_eq h_contra.1
              · exact h_lt
            linarith
          have h_k_lt_n : k < n := by
            have : k ≠ n := h_contra.2
            exact Nat.lt_of_dvd_of_lt hk_div (by linarith : 0 < n) this
          have h_k_sq_le_n : k * k ≤ n := by
            by_contra h_not
            push_neg at h_not
            have : ¬(k * k > n) := by linarith
            simp [is_prime.check_divisors] at h
            sorry
          sorry
        exact this
  · intro h
    simp [is_prime]
    split
    · simp [Nat.Prime] at h
      have : n ≥ 2 := Nat.Prime.two_le h
      linarith
    · simp
      sorry

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  simp [problem_spec]
  use implementation a
  constructor
  · rfl
  · intro h
    simp [implementation]
    split
    · rename_i h_lt
      simp [check_triple_prime_product]
      constructor
      · intro h_check
        split at h_check
        · simp at h_check
        · rename_i h_pos
          sorry
      · intro h_exists
        obtain ⟨a', b, c, ha_prime, hb_prime, hc_prime, h_eq⟩ := h_exists
        sorry
    · rename_i h_ge
      simp at h_ge
      have : ¬(a < 100) := by linarith
      contradiction