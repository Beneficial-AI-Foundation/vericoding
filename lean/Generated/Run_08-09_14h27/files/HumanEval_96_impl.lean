import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else
    let rec checkDivisors (d : Nat) : Bool :=
      if d * d > n then true
      else if n % d = 0 then false
      else checkDivisors (d + 2)
    termination_by n - d * d
    decreasing_by
      simp_wf
      have h1 : ¬d * d > n := by simp at *; assumption
      have h2 : ¬n % d = 0 := by simp at *; assumption
      have h3 : d * d ≤ n := Nat.le_of_not_gt h1
      have h4 : d + 2 > d := by omega
      have h5 : (d + 2) * (d + 2) > d * d := by
        have : d + 2 ≥ d + 1 := by omega
        have : (d + 2) * (d + 2) ≥ (d + 1) * (d + 1) := by
          apply Nat.mul_le_mul
          · omega
          · omega
        have : (d + 1) * (d + 1) = d * d + 2 * d + 1 := by ring
        have : (d + 2) * (d + 2) = d * d + 4 * d + 4 := by ring
        omega
    checkDivisors 3

-- LLM HELPER
def primesUpTo (n : Nat) : List Nat :=
  (List.range n).filter isPrime

def implementation (n: Nat) : List Nat :=
  primesUpTo n

-- LLM HELPER
lemma isPrime_correct (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    unfold isPrime at h
    by_cases h1 : n < 2
    · simp [h1] at h
    · by_cases h2 : n = 2
      · simp [h1, h2] at h
        rw [h2]
        exact Nat.prime_two
      · by_cases h3 : n % 2 = 0
        · simp [h1, h2, h3] at h
        · simp [h1, h2, h3] at h
          have h_ge_2 : n ≥ 2 := Nat.le_of_not_gt h1
          have h_ne_2 : n ≠ 2 := h2
          have h_odd : n % 2 ≠ 0 := h3
          constructor
          · omega
          · intro m hm hdiv
            by_cases hm_eq_1 : m = 1
            · left; exact hm_eq_1
            · right
              have : m = n := by
                by_contra h_ne
                have : m < n := Nat.lt_of_dvd_of_lt hdiv h_ge_2
                sorry
              exact this
  · intro h
    have h_prime := h
    unfold isPrime
    by_cases h1 : n < 2
    · have : n ≥ 2 := Nat.Prime.two_le h_prime
      omega
    · simp [h1]
      by_cases h2 : n = 2
      · simp [h2]
      · simp [h2]
        by_cases h3 : n % 2 = 0
        · have : Odd n := by
            cases' h_prime with hge hdiv
            rw [Nat.odd_iff_not_even]
            rw [Nat.even_iff_two_dvd]
            intro h_two_dvd
            have := hdiv 2 (by omega) h_two_dvd
            cases this with
            | inl h => omega
            | inr h => rw [h] at h2; contradiction
          rw [Nat.odd_iff_not_even] at this
          rw [Nat.even_iff_two_dvd] at this
          rw [Nat.dvd_iff_mod_eq_zero] at this
          contradiction
        · simp [h3]
          sorry

-- LLM HELPER
lemma primesUpTo_correct (n : Nat) :
  ∀ p ∈ primesUpTo n, Nat.Prime p ∧ p < n := by
  intro p hp
  simp [primesUpTo] at hp
  cases' hp with h1 h2
  constructor
  · rw [← isPrime_correct]
    exact h2
  · exact List.mem_range.mp h1

-- LLM HELPER
lemma primesUpTo_complete (n : Nat) :
  ∀ p : Nat, p < n → Nat.Prime p → p ∈ primesUpTo n := by
  intro p hp1 hp2
  simp [primesUpTo]
  constructor
  · exact List.mem_range.mpr hp1
  · rw [isPrime_correct]
    exact hp2

def problem_spec
-- function signature
(implementation: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result : List Nat) :=
  match n with
  | 0 => result = []
  | n => n > 0 → (∀ i, i < result.length → (Nat.Prime (result[i]!)) ∧ (result[i]!) < n) ∧
         (∀ i : Nat, i < n → Nat.Prime i → i ∈ result)
-- program termination
∃ result,
  implementation n = result ∧
  spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use primesUpTo n
  constructor
  · rfl
  · cases' n with n
    · simp [primesUpTo]
    · intro h
      constructor
      · intro i hi
        have hp : (primesUpTo n.succ)[i]! ∈ primesUpTo n.succ := by
          simp [List.getElem!_def]
          by_cases h_lt : i < (primesUpTo n.succ).length
          · exact List.getElem_mem (primesUpTo n.succ) i h_lt
          · simp [h_lt] at hi
        exact primesUpTo_correct n.succ (primesUpTo n.succ)[i]! hp
      · intro i hi hprime
        exact primesUpTo_complete n.succ i hi hprime