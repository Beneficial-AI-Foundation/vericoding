import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
let is_prime (n: Nat) : Prop :=
  ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
  result ↔ is_prime s.length
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def decidable_helper (n: Nat) (k: Nat) : Bool :=
  if k * k > n then true
  else if n % k = 0 then false
  else decidable_helper n (k + 1)
termination_by n + 1 - k
decreasing_by
  simp_wf
  have : k * k ≤ n := Nat.le_of_not_gt (by assumption)
  have : k < n := Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt this (Nat.lt_succ_self n)) (Nat.zero_le k)
  omega

-- LLM HELPER
def is_prime_decidable (n: Nat) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else decidable_helper n 2

-- LLM HELPER
lemma decidable_helper_correct (n k: Nat) (hk: k * k ≤ n) :
  decidable_helper n k = true → ¬ (∃ j, k ≤ j ∧ j * j ≤ n ∧ n % j = 0) := by
  intro h
  intro ⟨j, hj1, hj2, hj3⟩
  unfold decidable_helper at h
  split_ifs at h with h1 h2
  · omega
  · contradiction
  · have : k + 1 ≤ j := by
      by_contra h_contra
      have : j ≤ k := Nat.le_of_not_gt (Nat.not_lt.mpr (Nat.not_le.mp h_contra))
      have : j = k := Nat.eq_of_le_of_lt_succ this (Nat.lt_succ_iff.mpr hj1)
      rw [this] at hj3
      exact h2 hj3
    exact decidable_helper_correct n (k + 1) (by omega) h ⟨j, this, hj2, hj3⟩

-- LLM HELPER
lemma decidable_helper_correct_pos (n k: Nat) (hk: k * k ≤ n) :
  ¬ (∃ j, k ≤ j ∧ j * j ≤ n ∧ n % j = 0) → decidable_helper n k = true := by
  intro h
  unfold decidable_helper
  split_ifs with h1 h2
  · rfl
  · exfalso
    apply h
    use k
    exact ⟨le_refl k, hk, h2⟩
  · apply decidable_helper_correct_pos n (k + 1) (by omega)
    intro ⟨j, hj1, hj2, hj3⟩
    apply h
    use j
    exact ⟨Nat.le_trans (Nat.le_succ k) hj1, hj2, hj3⟩

-- LLM HELPER
lemma key_equivalence (n: Nat) (hn: n ≥ 2) :
  (¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0)) ↔ (¬ (∃ j, 2 ≤ j ∧ j * j ≤ n ∧ n % j = 0)) := by
  constructor
  · intro h ⟨j, hj1, hj2, hj3⟩
    apply h
    use j
    exact ⟨hj1, Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hj2 (Nat.lt_succ_self n)) (Nat.zero_le j), hj3⟩
  · intro h ⟨k, hk1, hk2, hk3⟩
    by_cases hc : k * k ≤ n
    · apply h
      use k
      exact ⟨hk1, hc, hk3⟩
    · have : n < k * k := Nat.lt_of_not_ge hc
      have : n / k < k := Nat.div_lt_iff_lt_mul_right (Nat.pos_of_ne_zero (ne_of_gt (Nat.pos_of_ne_zero (ne_of_gt hk1)))) |>.mpr this
      have : n / k * k ≤ n := Nat.div_mul_le_self n k
      have : n / k ≥ 2 := by
        have : k * 2 ≤ n := by
          by_contra h_contra
          have : n < k * 2 := Nat.lt_of_not_ge h_contra
          have : n / k < 2 := Nat.div_lt_iff_lt_mul_right (Nat.pos_of_ne_zero (ne_of_gt (Nat.pos_of_ne_zero (ne_of_gt hk1)))) |>.mpr this
          omega
        exact Nat.le_div_of_mul_le (Nat.pos_of_ne_zero (ne_of_gt (Nat.pos_of_ne_zero (ne_of_gt hk1)))) this
      have : n % (n / k) = 0 := by
        rw [Nat.mod_eq_zero_iff_dvd]
        use k * (k - n / k)
        omega
      apply h
      use n / k
      exact ⟨this, by omega, this⟩

-- LLM HELPER
lemma is_prime_decidable_correct (n: Nat) :
  is_prime_decidable n = true ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0) := by
  constructor
  · intro h
    intro ⟨k, hk⟩
    unfold is_prime_decidable at h
    cases' Nat.lt_or_ge n 2 with h1 h1
    · omega
    · cases' Nat.eq_or_lt_of_le h1 with h2 h2
      · rw [h2] at hk
        omega
      · simp [h1, h2] at h
        rw [key_equivalence n h1] at hk
        have := decidable_helper_correct n 2 (by omega) h
        exact this ⟨k, by omega, by omega, hk.2.2⟩
  · intro h
    unfold is_prime_decidable
    cases' Nat.lt_or_ge n 2 with h1 h1
    · omega
    · cases' Nat.eq_or_lt_of_le h1 with h2 h2
      · simp [h2]
      · simp [h1, h2]
        apply decidable_helper_correct_pos n 2 (by omega)
        rw [← key_equivalence n h1] at h
        intro ⟨j, hj1, hj2, hj3⟩
        apply h
        use j
        exact ⟨by omega, Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hj2 (Nat.lt_succ_self n)) (Nat.zero_le j), hj3⟩

def implementation (s: String) : Bool := is_prime_decidable s.length

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use is_prime_decidable s.length
  constructor
  · rfl
  · exact is_prime_decidable_correct s.length