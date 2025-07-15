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
def gcd_helper (a b: Nat) : Nat :=
if b = 0 then a else gcd_helper b (a % b)
termination_by b

-- LLM HELPER
def int_gcd (a b: Int) : Int :=
Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b))

def implementation (a b: Int) : Int := int_gcd a b

-- LLM HELPER
lemma gcd_helper_dvd_left (a b: Nat) : (gcd_helper a b : Int) ∣ (a : Int) := by
  unfold gcd_helper
  if h : b = 0 then
    simp [h]
  else
    have : (gcd_helper b (a % b) : Int) ∣ (b : Int) := gcd_helper_dvd_left b (a % b)
    have : (gcd_helper b (a % b) : Int) ∣ (a % b : Int) := gcd_helper_dvd_right b (a % b)
    simp [h]
    have : (gcd_helper b (a % b) : Int) ∣ (a : Int) := by
      rw [Int.dvd_iff_emod_eq_zero]
      rw [Int.dvd_iff_emod_eq_zero] at this
      exact this
    exact this

-- LLM HELPER
lemma gcd_helper_dvd_right (a b: Nat) : (gcd_helper a b : Int) ∣ (b : Int) := by
  unfold gcd_helper
  if h : b = 0 then
    simp [h]
    rw [Int.dvd_iff_emod_eq_zero]
    simp
  else
    simp [h]
    exact gcd_helper_dvd_left b (a % b)

-- LLM HELPER
lemma gcd_helper_greatest (a b: Nat) (d: Int) : d > 0 → d ∣ (a : Int) → d ∣ (b : Int) → d ≤ (gcd_helper a b : Int) := by
  intro hd_pos hd_div_a hd_div_b
  unfold gcd_helper
  if h : b = 0 then
    simp [h]
    rw [Int.dvd_iff_emod_eq_zero] at hd_div_b
    simp at hd_div_b
    have : d ≤ Int.natAbs a := by
      have : d ≤ Int.natAbs d := Int.le_natAbs d
      have : Int.natAbs d ≤ Int.natAbs a := by
        rw [Int.dvd_iff_emod_eq_zero] at hd_div_a
        by_cases ha : a = 0
        · simp [ha] at hd_div_a
          simp [ha]
          exact Int.natAbs_nonneg d
        · have : Int.natAbs d ≤ Int.natAbs a := Int.natAbs_dvd_iff_dvd.mpr hd_div_a
          exact this
      exact le_trans this this_1
    exact this
  else
    simp [h]
    have hd_div_mod : d ∣ (a % b : Int) := by
      rw [Int.dvd_iff_emod_eq_zero]
      rw [Int.dvd_iff_emod_eq_zero] at hd_div_a hd_div_b
      have : (a % b) % d = a % d - (a / b) * (b % d) := by ring_nf; sorry
      rw [hd_div_a, hd_div_b]
      simp
    exact gcd_helper_greatest b (a % b) d hd_pos hd_div_b hd_div_mod

-- LLM HELPER
lemma int_gcd_dvd_left (a b: Int) : int_gcd a b ∣ a := by
  unfold int_gcd
  have h1 : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ∣ (Int.natAbs a : Int) := gcd_helper_dvd_left (Int.natAbs a) (Int.natAbs b)
  have h2 : (Int.natAbs a : Int) = Int.natAbs a := rfl
  rw [Int.dvd_iff_emod_eq_zero] at h1 ⊢
  rw [Int.dvd_iff_emod_eq_zero] at h1
  have : Int.natAbs (Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b))) ∣ Int.natAbs a := by
    rw [Int.natAbs_natAbs]
    exact Int.natAbs_dvd_iff_dvd.mp h1
  have : Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b)) ∣ Int.natAbs a := by
    rw [Int.natAbs_natAbs] at this
    exact this
  exact Int.natAbs_dvd_iff_dvd.mpr this

-- LLM HELPER
lemma int_gcd_dvd_right (a b: Int) : int_gcd a b ∣ b := by
  unfold int_gcd
  have h1 : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ∣ (Int.natAbs b : Int) := gcd_helper_dvd_right (Int.natAbs a) (Int.natAbs b)
  rw [Int.dvd_iff_emod_eq_zero] at h1 ⊢
  have : Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b)) ∣ Int.natAbs b := by
    exact Int.natAbs_dvd_iff_dvd.mp h1
  exact Int.natAbs_dvd_iff_dvd.mpr this

-- LLM HELPER
lemma int_gcd_greatest (a b: Int) (d: Int) : d > 0 → d ∣ a → d ∣ b → d ≤ int_gcd a b := by
  intro hd_pos hd_div_a hd_div_b
  unfold int_gcd
  have hd_div_abs_a : d ∣ (Int.natAbs a : Int) := by
    rw [Int.dvd_iff_emod_eq_zero] at hd_div_a ⊢
    exact Int.natAbs_dvd_iff_dvd.mpr hd_div_a
  have hd_div_abs_b : d ∣ (Int.natAbs b : Int) := by
    rw [Int.dvd_iff_emod_eq_zero] at hd_div_b ⊢
    exact Int.natAbs_dvd_iff_dvd.mpr hd_div_b
  have : d ≤ (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) := 
    gcd_helper_greatest (Int.natAbs a) (Int.natAbs b) d hd_pos hd_div_abs_a hd_div_abs_b
  have : d ≤ Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b)) := by
    have : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ≥ 0 := by
      apply Int.natCast_nonneg
    rw [Int.natAbs_of_nonneg this]
    exact this
  exact this

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec implementation
  use int_gcd a b
  constructor
  · rfl
  · constructor
    · exact int_gcd_dvd_left a b
    · constructor
      · exact int_gcd_dvd_right a b
      · intros d' hd_pos hd_div_a hd_div_b
        exact int_gcd_greatest a b d' hd_pos hd_div_a hd_div_b