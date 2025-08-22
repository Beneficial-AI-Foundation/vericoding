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
  have h1 : ¬(k * k > n) := by assumption
  have h2 : ¬(n % k = 0) := by assumption
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
  simp only [decidable_helper] at h
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
  simp only [decidable_helper]
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
    have : j < n := by
      by_contra h_contra
      have : n ≤ j := Nat.le_of_not_gt h_contra
      have : j * j ≥ n * j := Nat.mul_le_mul_right j n
      have : n * j ≥ n * 2 := Nat.mul_le_mul_left n hj1
      have : n * 2 ≥ 2 * 2 := Nat.mul_le_mul_right 2 hn
      have : j * j ≥ 4 := by omega
      have : j ≥ 2 := by
        by_contra h_contra'
        have : j < 2 := Nat.lt_of_not_ge h_contra'
        have : j ≤ 1 := Nat.le_of_lt_succ h_contra'
        have : j * j ≤ 1 := by omega
        omega
      have : n ≤ j := by omega
      have : j * j ≥ n * n := by
        apply Nat.mul_le_mul'
        exact n
        exact n
      omega
    exact ⟨hj1, this, hj3⟩
  · intro h ⟨k, hk1, hk2, hk3⟩
    by_cases hc : k * k ≤ n
    · apply h
      use k
      exact ⟨hk1, hc, hk3⟩
    · have : n < k * k := Nat.lt_of_not_ge hc
      have hk_pos : k > 0 := by omega
      have : n / k < k := Nat.div_lt_iff_lt_mul_right hk_pos |>.mpr this
      have : n / k * k ≤ n := Nat.div_mul_le_self n k
      have : n / k ≥ 2 := by
        have : k * 2 ≤ n := by
          by_contra h_contra
          have : n < k * 2 := Nat.lt_of_not_ge h_contra
          have : n / k < 2 := Nat.div_lt_iff_lt_mul_right hk_pos |>.mpr this
          omega
        exact Nat.le_div_of_mul_le hk_pos this
      have : n % (n / k) = 0 := by
        have : (n / k) ∣ n := by
          use k
          have : n = (n / k) * k + n % k := Nat.div_add_mod n k
          rw [hk3] at this
          omega
        exact Nat.mod_eq_zero_of_dvd this
      apply h
      use n / k
      exact ⟨this, by omega, this⟩

-- LLM HELPER
lemma is_prime_decidable_correct (n: Nat) :
  is_prime_decidable n = true ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0) := by
  constructor
  · intro h
    intro ⟨k, hk⟩
    simp only [is_prime_decidable] at h
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
    simp only [is_prime_decidable]
    cases' Nat.lt_or_ge n 2 with h1 h1
    · simp [h1]
      exfalso
      apply h
      use 1
      omega
    · cases' Nat.eq_or_lt_of_le h1 with h2 h2
      · simp [h2]
      · simp [h1, h2]
        apply decidable_helper_correct_pos n 2 (by omega)
        rw [← key_equivalence n h1] at h
        intro ⟨j, hj1, hj2, hj3⟩
        apply h
        use j
        have : j < n := by
          by_contra h_contra
          have : n ≤ j := Nat.le_of_not_gt h_contra
          have : j * j ≥ n * j := Nat.mul_le_mul_right j n
          have : n * j ≥ n * 2 := Nat.mul_le_mul_left n (by omega)
          have : n * 2 ≥ 2 * 2 := Nat.mul_le_mul_right 2 h1
          omega
        exact ⟨by omega, this, hj3⟩

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