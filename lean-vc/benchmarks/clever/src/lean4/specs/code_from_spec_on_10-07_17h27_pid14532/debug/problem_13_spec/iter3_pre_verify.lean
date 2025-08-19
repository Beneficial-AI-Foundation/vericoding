import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) :=
-- spec
let spec (result: Int) :=
(result ∣ a) ∧
(result ∣ b) ∧
(∀ (d': Int),
(d' > 0) → (d' ∣ a) → (d' ∣ b) →
d' ≤ result);
-- program termination
∃ result, implementation a b = result ∧
spec result

-- LLM HELPER
def gcd_aux : Int → Int → Int
| a, 0 => Int.natAbs a
| a, b => gcd_aux b (a % b)
termination_by a b => Int.natAbs b

def implementation (a b: Int) : Int := gcd_aux a b

-- LLM HELPER
lemma gcd_aux_dvd_left (a b : Int) : (gcd_aux a b : Int) ∣ a := by
  unfold gcd_aux
  if h : b = 0 then
    simp [h, gcd_aux]
    exact Int.natAbs_dvd_iff_dvd.mp (dvd_refl _)
  else
    have : Int.natAbs b < Int.natAbs b ∨ Int.natAbs b = 0 := by
      by_cases h' : b = 0
      · right; simp [h']
      · left; simp [h']
    induction' Int.natAbs b using Nat.strong_induction_on with n ih
    cases' n with n
    · simp [gcd_aux]
    · rw [gcd_aux]
      split
      · simp
        exact Int.natAbs_dvd_iff_dvd.mp (dvd_refl _)
      · have h_rec := ih (Int.natAbs (a % b)) (by simp; exact Int.natAbs_mod_lt _ h) (a % b)
        rw [dvd_iff_emod_eq_zero] at h_rec ⊢
        rw [Int.emod_emod_of_dvd _ h_rec]

-- LLM HELPER
lemma gcd_aux_dvd_right (a b : Int) : (gcd_aux a b : Int) ∣ b := by
  unfold gcd_aux
  if h : b = 0 then
    simp [h, gcd_aux]
  else
    induction' Int.natAbs b using Nat.strong_induction_on with n ih
    cases' n with n
    · simp [gcd_aux]
    · rw [gcd_aux]
      split
      · simp
      · exact gcd_aux_dvd_left b (a % b)

-- LLM HELPER
lemma gcd_aux_pos (a b : Int) (ha : a ≠ 0 ∨ b ≠ 0) : (gcd_aux a b : Int) > 0 := by
  unfold gcd_aux
  if h : b = 0 then
    simp [h, gcd_aux]
    cases' ha with h_a h_b
    · exact Int.natAbs_pos.mpr h_a
    · contradiction
  else
    induction' Int.natAbs b using Nat.strong_induction_on with n ih
    cases' n with n
    · simp [gcd_aux]
      cases' ha with h_a h_b
      · exact Int.natAbs_pos.mpr h_a
      · contradiction
    · rw [gcd_aux]
      split
      · simp
        cases' ha with h_a h_b
        · exact Int.natAbs_pos.mpr h_a
        · contradiction
      · apply ih (Int.natAbs (a % b)) (by simp; exact Int.natAbs_mod_lt _ h) (a % b)
        right
        exact Int.emod_two_eq_zero_or_one a ▸ Int.one_pos

-- LLM HELPER
lemma gcd_aux_greatest (a b : Int) (d : Int) (hd_pos : d > 0) (hd_a : d ∣ a) (hd_b : d ∣ b) : d ≤ gcd_aux a b := by
  unfold gcd_aux
  if h : b = 0 then
    simp [h, gcd_aux]
    exact Int.le_natAbs_of_nonneg (le_of_lt hd_pos) ▸ Int.natAbs_dvd_iff_dvd.mpr hd_a
  else
    induction' Int.natAbs b using Nat.strong_induction_on with n ih
    cases' n with n
    · simp [gcd_aux]
      exact Int.le_natAbs_of_nonneg (le_of_lt hd_pos)
    · rw [gcd_aux]
      split
      · simp
        exact Int.le_natAbs_of_nonneg (le_of_lt hd_pos)
      · apply ih (Int.natAbs (a % b)) (by simp; exact Int.natAbs_mod_lt _ h) (a % b)
        · exact hd_pos
        · exact hd_b
        · rw [dvd_iff_emod_eq_zero] at hd_a hd_b ⊢
          rw [Int.sub_emod, hd_a, hd_b, zero_sub, Int.neg_emod, Int.emod_self, neg_zero]

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec implementation
  use gcd_aux a b
  constructor
  · rfl
  · constructor
    · exact gcd_aux_dvd_left a b
    · constructor
      · exact gcd_aux_dvd_right a b
      · intros d' hd'_pos hd'_a hd'_b
        exact gcd_aux_greatest a b d' hd'_pos hd'_a hd'_b