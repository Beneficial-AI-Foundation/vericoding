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
termination_by gcd_aux a b => Int.natAbs b

def implementation (a b: Int) : Int := gcd_aux a b

-- LLM HELPER
lemma gcd_aux_dvd_left (a b : Int) : (gcd_aux a b : Int) ∣ a := by
  induction' b using Int.natAbs_ind with b ih
  · simp [gcd_aux]
  · rw [gcd_aux]
    have h := ih (a % b)
    rw [dvd_iff_emod_eq_zero] at h ⊢
    rw [Int.emod_emod_of_dvd _ h]

-- LLM HELPER
lemma gcd_aux_dvd_right (a b : Int) : (gcd_aux a b : Int) ∣ b := by
  induction' b using Int.natAbs_ind with b ih
  · simp [gcd_aux]
  · rw [gcd_aux]
    exact gcd_aux_dvd_left b (a % b)

-- LLM HELPER
lemma gcd_aux_pos (a b : Int) (ha : a ≠ 0 ∨ b ≠ 0) : (gcd_aux a b : Int) > 0 := by
  induction' b using Int.natAbs_ind with b ih
  · simp [gcd_aux]
    cases' ha with h h
    · exact Int.natAbs_pos.mpr h
    · contradiction
  · rw [gcd_aux]
    apply ih
    right
    exact Int.emod_two_eq_zero_or_one a ▸ Int.one_pos

-- LLM HELPER
lemma gcd_aux_greatest (a b : Int) (d : Int) (hd_pos : d > 0) (hd_a : d ∣ a) (hd_b : d ∣ b) : d ≤ gcd_aux a b := by
  induction' b using Int.natAbs_ind with b ih
  · simp [gcd_aux]
    exact Int.natAbs_of_nonneg (le_of_lt hd_pos) ▸ Int.natAbs_dvd_iff_dvd.mpr hd_a ▸ 
          Int.le_natAbs_of_nonneg (le_of_lt hd_pos)
  · rw [gcd_aux]
    apply ih
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