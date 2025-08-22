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
  1 < n ∧ ¬ Nat.Prime n →
  (Nat.Prime result ∧ result ∣ n ∧
  ∀ i, i < n ∧ i ∣ n ∧ Nat.Prime i → i ≤ result);
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def findLargestPrimeFactor (n: Nat) : Nat :=
  if n ≤ 1 then 0
  else
    let rec aux (i: Nat) (largest: Nat) : Nat :=
      if i > n then largest
      else if i ∣ n ∧ Nat.Prime i then
        aux (i + 1) i
      else
        aux (i + 1) largest
    termination_by n + 1 - i
    aux 2 0

def implementation (n: Nat) : Nat := findLargestPrimeFactor n

-- LLM HELPER
lemma aux_spec (n i largest: Nat) (h_bound: i ≤ n + 1) :
  let result := findLargestPrimeFactor.aux n i largest
  (largest = 0 ∨ (Nat.Prime largest ∧ largest ∣ n)) →
  (∃ j, j ≥ i ∧ j ≤ n ∧ Nat.Prime j ∧ j ∣ n) ∨ largest ≠ 0 →
  (result = 0 ∨ (Nat.Prime result ∧ result ∣ n ∧ ∀ k, k ≤ n ∧ k ∣ n ∧ Nat.Prime k → k ≤ result)) := by
  intro h_largest h_exists
  induction' Nat.sub (n + 1) i using Nat.strong_induction_on with m ih generalizing i largest
  unfold findLargestPrimeFactor.aux
  split_ifs with h_gt h_div_prime
  · -- Case: i > n
    intro h_cond
    cases' h_largest with h_zero h_pos
    · -- largest = 0
      cases' h_cond with h_ex h_ne
      · -- There exists a prime factor ≥ i
        obtain ⟨j, hj_ge, hj_le, hj_prime, hj_div⟩ := h_ex
        -- But i > n and j ≤ n, so j < i, contradiction
        have : j < i := lt_of_le_of_lt hj_le (Nat.lt_of_succ_le (Nat.succ_le_of_lt h_gt))
        omega
      · -- largest ≠ 0, but largest = 0
        exfalso
        exact h_ne h_zero
    · -- largest is prime and divides n
      right
      constructor
      · exact h_pos.1
      · constructor
        · exact h_pos.2
        · intros k hk
          exact h_pos.2.2 k hk
  · -- Case: i ≤ n and i divides n and is prime
    have h_le : i ≤ n := Nat.le_of_not_gt h_gt
    have h_prime : Nat.Prime i := h_div_prime.2
    have h_div : i ∣ n := h_div_prime.1
    have h_bound_new : i + 1 ≤ n + 1 := by omega
    have h_decrease : n + 1 - (i + 1) < m := by
      simp only [m]
      omega
    intro h_cond
    apply ih (n + 1 - (i + 1)) h_decrease (i + 1) i h_bound_new
    · right
      exact ⟨h_prime, h_div⟩
    · left
      use i, le_refl i, h_le, h_prime, h_div
  · -- Case: i ≤ n and (i does not divide n or i is not prime)
    have h_le : i ≤ n := Nat.le_of_not_gt h_gt
    have h_bound_new : i + 1 ≤ n + 1 := by omega
    have h_decrease : n + 1 - (i + 1) < m := by
      simp only [m]
      omega
    intro h_cond
    apply ih (n + 1 - (i + 1)) h_decrease (i + 1) largest h_bound_new h_largest
    cases' h_exists with h_ex h_ne
    · left
      obtain ⟨j, hj_ge, hj_le, hj_prime, hj_div⟩ := h_ex
      if h_eq : j = i then
        subst h_eq
        have : i ∣ n ∧ Nat.Prime i := ⟨hj_div, hj_prime⟩
        contradiction
      else
        have : j ≥ i + 1 := by
          have : j ≥ i := hj_ge
          have : j ≠ i := h_eq
          omega
        use j, this, hj_le, hj_prime, hj_div
    · right
      exact h_ne

-- LLM HELPER
lemma findLargestPrimeFactor_spec (n: Nat) :
  1 < n ∧ ¬ Nat.Prime n →
  let result := findLargestPrimeFactor n
  (Nat.Prime result ∧ result ∣ n ∧
  ∀ i, i < n ∧ i ∣ n ∧ Nat.Prime i → i ≤ result) := by
  intro h
  unfold findLargestPrimeFactor
  split_ifs with h1
  · simp at h1
    omega
  · have : ∃ p, Nat.Prime p ∧ p ∣ n := by
      have : ¬ Nat.Prime n := h.2
      have : 1 < n := h.1
      exact Nat.exists_prime_divisor (ne_of_gt h.1)
    obtain ⟨p, hp_prime, hp_div⟩ := this
    
    have h_exists : (∃ j, j ≥ 2 ∧ j ≤ n ∧ Nat.Prime j ∧ j ∣ n) ∨ 0 ≠ 0 := by
      left
      have : p ≥ 2 := Nat.Prime.two_le hp_prime
      use p, this, (Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_of_gt h.1)) hp_div), hp_prime, hp_div
    
    have aux_result := aux_spec n 2 0 (by omega) (by left; rfl) h_exists
    cases' aux_result with h_zero h_pos
    · exfalso
      have : ∃ j, j ≥ 2 ∧ j ≤ n ∧ Nat.Prime j ∧ j ∣ n := h_exists.resolve_right (by simp)
      obtain ⟨j, hj_ge, hj_le, hj_prime, hj_div⟩ := this
      -- The aux function should find this prime factor but returned 0
      have : findLargestPrimeFactor.aux n 2 0 ≠ 0 := by
        have aux_correct := aux_spec n 2 0 (by omega)
        have h_largest : (0 : Nat) = 0 ∨ (Nat.Prime 0 ∧ 0 ∣ n) := by left; rfl
        have h_ex : (∃ j, j ≥ 2 ∧ j ≤ n ∧ Nat.Prime j ∧ j ∣ n) ∨ 0 ≠ 0 := by
          left
          use j, hj_ge, hj_le, hj_prime, hj_div
        have result := aux_correct h_largest h_ex
        cases' result with h_zero_case h_pos_case
        · exfalso
          -- If result is 0, then there must be no prime factors found
          simp at h_zero_case
          -- But we know there exists a prime factor j
          have : j ≥ 2 ∧ j ≤ n ∧ Nat.Prime j ∧ j ∣ n := ⟨hj_ge, hj_le, hj_prime, hj_div⟩
          -- This contradicts the aux function behavior
          rw [h_zero_case] at h_zero
          exact h_zero
        · rw [h_zero] at h_pos_case
          simp at h_pos_case
      rw [h_zero] at this
      simp at this
    · constructor
      · exact h_pos.1
      · constructor
        · exact h_pos.2.1
        · intros i hi
          have : i ≤ n := Nat.le_of_lt hi.1
          exact h_pos.2.2 i ⟨this, hi.2.1, hi.2.2⟩

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  use implementation n
  constructor
  · rfl
  · exact findLargestPrimeFactor_spec n