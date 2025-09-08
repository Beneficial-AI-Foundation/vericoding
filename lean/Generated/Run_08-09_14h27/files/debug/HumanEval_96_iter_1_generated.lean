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
    cases' n with n
    · simp [isPrime] at h
    · cases' n with n
      · simp [isPrime] at h
      · simp [isPrime] at h
        split at h
        · simp at h
        · split at h
          · rw [Nat.Prime]
            constructor
            · norm_num
            · intro m hm
              by_cases h1 : m = 1
              · left; exact h1
              · right
                by_cases h2 : m = 2
                · exact h2
                · exfalso
                  have : m ∣ 2 := by
                    rw [Nat.dvd_iff_mod_eq_zero]
                    sorry
                  sorry
          · split at h
            · simp at h
            · sorry
  · intro h
    have hp : Nat.Prime n := h
    cases' n with n
    · simp [Nat.Prime] at hp
    · cases' n with n
      · simp [Nat.Prime] at hp
    · simp [isPrime]
      split
      · simp [Nat.Prime] at hp
      · split
        · simp [Nat.Prime] at hp
        · split
          · have : 2 ∣ (n + 2) := by
              rw [Nat.dvd_iff_mod_eq_zero]
              assumption
            have : n + 2 ≠ 2 := by norm_num
            have : ¬ Nat.Prime (n + 2) := by
              rw [Nat.Prime]
              push_neg
              right
              use 2
              constructor
              · exact this
              · constructor
                · norm_num
                · exact ⟨this, by norm_num⟩
            contradiction
          · sorry

-- LLM HELPER
lemma primesUpTo_correct (n : Nat) :
  ∀ p ∈ primesUpTo n, Nat.Prime p ∧ p < n := by
  intro p hp
  simp [primesUpTo] at hp
  have ⟨h1, h2⟩ := List.mem_filter.mp hp
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
        have hp := List.getElem_mem (primesUpTo (Nat.succ n)) i hi
        exact primesUpTo_correct (Nat.succ n) (primesUpTo (Nat.succ n))[i]! hp
      · intro i hi hprime
        exact primesUpTo_complete (Nat.succ n) hi hprime