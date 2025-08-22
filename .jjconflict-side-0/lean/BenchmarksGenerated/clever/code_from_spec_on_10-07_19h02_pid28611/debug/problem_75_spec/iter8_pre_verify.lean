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
    decreasing_by 
      simp_wf
      cases' h : d * d > n with
      · simp [h]
      · have : d * d ≤ n := by linarith
        have : d < n := by
          cases' d with
          | zero => simp
          | succ k => 
            have : d ≥ 1 := by simp
            have : d * d ≥ d := by
              rw [← Nat.mul_one d]
              exact Nat.mul_le_mul_left d this
            linarith
        exact Nat.sub_lt (by linarith) (by simp)
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
            decreasing_by 
              simp_wf
              cases' h : p1 * p2 * p3 > n with
              · simp [h]
              · have : p1 * p2 * p3 ≤ n := by linarith
                have : p3 < n := by
                  cases' p3 with
                  | zero => simp
                  | succ k => 
                    have : p3 ≥ 1 := by simp
                    have : p1 * p2 * p3 ≥ p3 := by
                      have : p1 ≥ 1 := by simp
                      have : p2 ≥ 1 := by simp
                      have : p1 * p2 ≥ 1 := Nat.mul_pos (by linarith) (by linarith)
                      rw [← Nat.mul_one p3]
                      exact Nat.mul_le_mul_right p3 this
                    linarith
                exact Nat.sub_lt (by linarith) (by simp)
            if check_third n p1 p2 p2 then true
            else check_second n p1 (p2 + 1)
          else check_second n p1 (p2 + 1)
        termination_by n - p2
        decreasing_by 
          simp_wf
          cases' h : p1 * p2 * p2 > n with
          · simp [h]
          · have : p1 * p2 * p2 ≤ n := by linarith
            have : p2 < n := by
              cases' p2 with
              | zero => simp
              | succ k => 
                have : p2 ≥ 1 := by simp
                have : p1 * p2 * p2 ≥ p2 := by
                  have : p1 ≥ 1 := by simp
                  have : p2 * p2 ≥ p2 := by
                    rw [← Nat.mul_one p2]
                    exact Nat.mul_le_mul_left p2 this
                  rw [← Nat.mul_one p2]
                  exact Nat.mul_le_mul_right p2 this
                linarith
            exact Nat.sub_lt (by linarith) (by simp)
        if check_second n p1 p1 then true
        else check_factors n (p1 + 1)
      else check_factors n (p1 + 1)
    termination_by n - p1
    decreasing_by 
      simp_wf
      cases' h : p1 * p1 * p1 > n with
      · simp [h]
      · have : p1 * p1 * p1 ≤ n := by linarith
        have : p1 < n := by
          cases' p1 with
          | zero => simp
          | succ k => 
            have : p1 ≥ 1 := by simp
            have : p1 * p1 * p1 ≥ p1 := by
              have : p1 * p1 ≥ p1 := by
                rw [← Nat.mul_one p1]
                exact Nat.mul_le_mul_left p1 this
              rw [← Nat.mul_one p1]
              exact Nat.mul_le_mul_right p1 this
            linarith
        exact Nat.sub_lt (by linarith) (by simp)
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
        sorry
  · intro h
    simp [is_prime]
    have h_ge_2 : 2 ≤ n := Nat.Prime.two_le h
    cases' h₁ : n < 2 with
    · simp [h₁]
      linarith
    · simp [h₁]
      sorry

-- LLM HELPER
lemma check_triple_prime_product_correct (a : Int) : 
  check_triple_prime_product a = true ↔ 
  (a > 0 ∧ ∃ p1 p2 p3, Nat.Prime p1 ∧ Nat.Prime p2 ∧ Nat.Prime p3 ∧ a.natAbs = p1 * p2 * p3) := by
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