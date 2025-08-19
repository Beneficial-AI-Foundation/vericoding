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
decreasing_by
  simp_wf
  exact Int.natAbs_mod_lt _ (by assumption)

def implementation (a b: Int) : Int := gcd_aux a b

-- LLM HELPER
lemma gcd_aux_dvd_left (a b : Int) : (gcd_aux a b : Int) ∣ a := by
  wf_induction a b using gcd_aux.induct
  case case1 a =>
    simp [gcd_aux]
    exact Int.natAbs_dvd_iff_dvd.mp (dvd_refl _)
  case case2 a b h ih =>
    simp [gcd_aux, h]
    have h1 : gcd_aux b (a % b) ∣ b := by
      exact ih
    have h2 : gcd_aux b (a % b) ∣ (a % b) := by
      have : (gcd_aux (a % b) b : Int) ∣ (a % b) := by
        cases' Classical.em (b = 0) with hb hb
        · simp [hb, gcd_aux]
          exact Int.natAbs_dvd_iff_dvd.mp (dvd_refl _)
        · exact ih
      exact this
    have : a = (a / b) * b + (a % b) := Int.emod_add_ediv a b
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) h2

-- LLM HELPER
lemma gcd_aux_dvd_right (a b : Int) : (gcd_aux a b : Int) ∣ b := by
  wf_induction a b using gcd_aux.induct
  case case1 a =>
    simp [gcd_aux]
    exact dvd_zero _
  case case2 a b h ih =>
    simp [gcd_aux, h]
    exact ih

-- LLM HELPER
lemma gcd_aux_pos (a b : Int) (ha : a ≠ 0 ∨ b ≠ 0) : (gcd_aux a b : Int) > 0 := by
  wf_induction a b using gcd_aux.induct
  case case1 a =>
    simp [gcd_aux]
    cases' ha with h_a h_b
    · exact Int.natAbs_pos.mpr h_a
    · simp at h_b
      exact Int.natAbs_pos.mpr h_a
  case case2 a b h ih =>
    simp [gcd_aux, h]
    apply ih
    right
    exact h

-- LLM HELPER
lemma gcd_aux_greatest (a b : Int) (d : Int) (hd_pos : d > 0) (hd_a : d ∣ a) (hd_b : d ∣ b) : d ≤ gcd_aux a b := by
  wf_induction a b using gcd_aux.induct
  case case1 a =>
    simp [gcd_aux]
    exact Int.le_natAbs_of_nonneg (le_of_lt hd_pos) ▸ Int.natAbs_dvd_iff_dvd.mpr hd_a
  case case2 a b h ih =>
    simp [gcd_aux, h]
    apply ih
    · exact hd_pos
    · exact hd_b
    · have : a = (a / b) * b + (a % b) := Int.emod_add_ediv a b
      rw [dvd_iff_emod_eq_zero] at hd_a hd_b
      rw [dvd_iff_emod_eq_zero]
      have : (a % b) % d = ((a / b) * b + (a % b)) % d - ((a / b) * b) % d := by
        rw [Int.add_sub_cancel]
      rw [← this, ← Int.emod_add_ediv a b, hd_a, zero_sub, Int.neg_emod]
      rw [Int.mul_emod, hd_b, zero_mul, zero_emod]

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