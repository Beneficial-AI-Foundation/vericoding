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
    aux 2 0

def implementation (n: Nat) : Nat := findLargestPrimeFactor n

-- LLM HELPER
lemma findLargestPrimeFactor_spec (n: Nat) :
  1 < n ∧ ¬ Nat.Prime n →
  let result := findLargestPrimeFactor n
  (Nat.Prime result ∧ result ∣ n ∧
  ∀ i, i < n ∧ i ∣ n ∧ Nat.Prime i → i ≤ result) := by
  intro h
  simp [findLargestPrimeFactor]
  split_ifs with h1
  · simp at h1
    omega
  · simp only [findLargestPrimeFactor]
    simp [h1]
    have : ∃ p, Nat.Prime p ∧ p ∣ n := by
      have : ¬ Nat.Prime n := h.2
      have : 1 < n := h.1
      exact Nat.exists_prime_factor this ‹1 < n›
    obtain ⟨p, hp_prime, hp_div⟩ := this
    have aux_terminates : ∀ i largest, i ≤ n + 1 → 
      let result := findLargestPrimeFactor.aux n i largest
      (largest = 0 ∨ (Nat.Prime largest ∧ largest ∣ n)) →
      (∃ j, j ≥ i ∧ j ≤ n ∧ Nat.Prime j ∧ j ∣ n) ∨ largest ≠ 0 →
      Nat.Prime result ∧ result ∣ n ∧ ∀ k, k < n ∧ k ∣ n ∧ Nat.Prime k → k ≤ result := by
      intro i largest hi hlargest hexists
      induction' i using Nat.strong_induction_on with i ih generalizing largest
      simp only [findLargestPrimeFactor.aux]
      split_ifs with hi_gt
      · cases' hlargest with h0 hpos
        · simp at h0
          subst h0
          cases' hexists with hex _
          · obtain ⟨j, hj_ge, hj_le, hj_prime, hj_div⟩ := hex
            have : j ≥ i := hj_ge
            have : i > n := hi_gt
            have : j ≤ n := hj_le
            omega
          · contradiction
        · exact hpos
      · have hi_le : i ≤ n := Nat.le_of_not_gt hi_gt
        split_ifs with hi_cond
        · have hi_prime : Nat.Prime i := hi_cond.2
          have hi_div : i ∣ n := hi_cond.1
          have : i + 1 ≤ n + 1 := by omega
          apply ih (i + 1) (by omega) i this
          · right
            exact ⟨hi_prime, hi_div⟩
          · left
            use i, le_refl i, hi_le, hi_prime, hi_div
        · have : i + 1 ≤ n + 1 := by omega
          apply ih (i + 1) (by omega) largest this hlargest
          cases' hexists with hex hne
          · left
            obtain ⟨j, hj_ge, hj_le, hj_prime, hj_div⟩ := hex
            if hj_eq : j = i then
              subst hj_eq
              have : i ∣ n ∧ Nat.Prime i := ⟨hj_div, hj_prime⟩
              contradiction
            else
              have : j ≥ i + 1 := by
                have : j ≥ i := hj_ge
                have : j ≠ i := hj_eq
                omega
              use j, this, hj_le, hj_prime, hj_div
          · right
            exact hne
    
    have : (∃ j, j ≥ 2 ∧ j ≤ n ∧ Nat.Prime j ∧ j ∣ n) ∨ 0 ≠ 0 := by
      left
      have : p ≥ 2 := Nat.Prime.two_le hp_prime
      use p, this, (Nat.le_of_dvd ‹1 < n› hp_div), hp_prime, hp_div
    
    apply aux_terminates 2 0 (by omega) (by left; rfl) this

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  use implementation n
  constructor
  · rfl
  · exact findLargestPrimeFactor_spec n