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
decreasing_by simp_wf; exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹b ≠ 0›)

-- LLM HELPER
def int_gcd (a b: Int) : Int :=
Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b))

def implementation (a b: Int) : Int := int_gcd a b

-- LLM HELPER
lemma gcd_helper_dvd_left (a b: Nat) : (gcd_helper a b : Int) ∣ (a : Int) := by
  induction' b using Nat.strongInductionOn with b ih generalizing a
  rw [gcd_helper]
  if h : b = 0 then
    simp [h]
  else
    simp [h]
    have h_mod : a % b < b := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    have ih_call := ih (a % b) h_mod b
    have ih_call2 := ih (a % b) h_mod (a % b)
    have dvd_b : (gcd_helper b (a % b) : Int) ∣ (b : Int) := ih_call
    have dvd_mod : (gcd_helper b (a % b) : Int) ∣ (a % b : Int) := ih_call2
    rw [Int.dvd_iff_emod_eq_zero] at dvd_b dvd_mod ⊢
    have : (a : Int) = (a / b : Int) * (b : Int) + (a % b : Int) := by
      rw [Int.emod_add_ediv_cancel]
    rw [this]
    rw [Int.add_mul_emod_self_left]
    exact dvd_mod

-- LLM HELPER
lemma gcd_helper_dvd_right (a b: Nat) : (gcd_helper a b : Int) ∣ (b : Int) := by
  induction' b using Nat.strongInductionOn with b ih generalizing a
  rw [gcd_helper]
  if h : b = 0 then
    simp [h]
  else
    simp [h]
    have h_mod : a % b < b := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    exact ih (a % b) h_mod b

-- LLM HELPER
lemma gcd_helper_greatest (a b: Nat) (d: Int) : d > 0 → d ∣ (a : Int) → d ∣ (b : Int) → d ≤ (gcd_helper a b : Int) := by
  intro hd_pos hd_div_a hd_div_b
  induction' b using Nat.strongInductionOn with b ih generalizing a
  rw [gcd_helper]
  if h : b = 0 then
    simp [h]
    rw [Int.dvd_iff_emod_eq_zero] at hd_div_b
    simp at hd_div_b
    have : d ≤ Int.natAbs a := by
      have : Int.natAbs d ≤ Int.natAbs a := by
        rw [Int.dvd_iff_emod_eq_zero] at hd_div_a
        by_cases ha : a = 0
        · simp [ha] at hd_div_a
          simp [ha]
          exact Int.natAbs_nonneg d
        · exact Int.natAbs_dvd_natAbs hd_div_a
      rw [Int.natAbs_of_nonneg (le_of_lt hd_pos)]
      exact this
    exact Int.coe_nat_le_coe_nat_iff.mpr this
  else
    simp [h]
    have h_mod : a % b < b := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    have hd_div_mod : d ∣ (a % b : Int) := by
      rw [Int.dvd_iff_emod_eq_zero] at hd_div_a hd_div_b ⊢
      have : (a : Int) = (a / b : Int) * (b : Int) + (a % b : Int) := by
        rw [Int.emod_add_ediv_cancel]
      rw [this] at hd_div_a
      rw [Int.add_mul_emod_self_left] at hd_div_a
      exact hd_div_a
    exact ih (a % b) h_mod b hd_pos hd_div_b hd_div_mod

-- LLM HELPER
lemma int_gcd_dvd_left (a b: Int) : int_gcd a b ∣ a := by
  unfold int_gcd
  have h1 : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ∣ (Int.natAbs a : Int) := gcd_helper_dvd_left (Int.natAbs a) (Int.natAbs b)
  rw [Int.dvd_iff_emod_eq_zero] at h1 ⊢
  have : Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b)) ∣ Int.natAbs a := by
    have : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ≥ 0 := Int.natCast_nonneg _
    rw [Int.natAbs_of_nonneg this]
    exact Int.natAbs_dvd_natAbs h1
  exact Int.dvd_natAbs.mp this

-- LLM HELPER
lemma int_gcd_dvd_right (a b: Int) : int_gcd a b ∣ b := by
  unfold int_gcd
  have h1 : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ∣ (Int.natAbs b : Int) := gcd_helper_dvd_right (Int.natAbs a) (Int.natAbs b)
  rw [Int.dvd_iff_emod_eq_zero] at h1 ⊢
  have : Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b)) ∣ Int.natAbs b := by
    have : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ≥ 0 := Int.natCast_nonneg _
    rw [Int.natAbs_of_nonneg this]
    exact Int.natAbs_dvd_natAbs h1
  exact Int.dvd_natAbs.mp this

-- LLM HELPER
lemma int_gcd_greatest (a b: Int) (d: Int) : d > 0 → d ∣ a → d ∣ b → d ≤ int_gcd a b := by
  intro hd_pos hd_div_a hd_div_b
  unfold int_gcd
  have hd_div_abs_a : d ∣ (Int.natAbs a : Int) := Int.dvd_natAbs.mpr hd_div_a
  have hd_div_abs_b : d ∣ (Int.natAbs b : Int) := Int.dvd_natAbs.mpr hd_div_b
  have h1 : d ≤ (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) := 
    gcd_helper_greatest (Int.natAbs a) (Int.natAbs b) d hd_pos hd_div_abs_a hd_div_abs_b
  have h2 : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ≥ 0 := Int.natCast_nonneg _
  rw [Int.natAbs_of_nonneg h2]
  exact h1

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