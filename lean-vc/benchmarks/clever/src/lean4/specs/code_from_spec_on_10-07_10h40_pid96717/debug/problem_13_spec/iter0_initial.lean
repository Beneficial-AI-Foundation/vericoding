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
def natGcd (a b : Nat) : Nat := Nat.gcd a b

-- LLM HELPER
def intGcd (a b : Int) : Int := Int.natAbs (natGcd (Int.natAbs a) (Int.natAbs b))

def implementation (a b: Int) : Int := intGcd a b

-- LLM HELPER
lemma int_gcd_dvd_left (a b : Int) : intGcd a b ∣ a := by
  unfold intGcd
  rw [Int.dvd_iff_natAbs_dvd_natAbs]
  exact Nat.gcd_dvd_left (Int.natAbs a) (Int.natAbs b)

-- LLM HELPER
lemma int_gcd_dvd_right (a b : Int) : intGcd a b ∣ b := by
  unfold intGcd
  rw [Int.dvd_iff_natAbs_dvd_natAbs]
  exact Nat.gcd_dvd_right (Int.natAbs a) (Int.natAbs b)

-- LLM HELPER
lemma int_gcd_pos (a b : Int) (h : a ≠ 0 ∨ b ≠ 0) : intGcd a b > 0 := by
  unfold intGcd
  simp only [Int.natCast_pos]
  apply Nat.gcd_pos_of_pos_left
  cases h with
  | inl ha => exact Int.natAbs_pos.mpr ha
  | inr hb => exact Int.natAbs_pos.mpr hb

-- LLM HELPER
lemma int_gcd_greatest (a b d : Int) (hd_pos : d > 0) (hd_a : d ∣ a) (hd_b : d ∣ b) : d ≤ intGcd a b := by
  unfold intGcd
  have h1 : Int.natAbs d ∣ Int.natAbs a := by
    rw [← Int.dvd_iff_natAbs_dvd_natAbs]
    exact hd_a
  have h2 : Int.natAbs d ∣ Int.natAbs b := by
    rw [← Int.dvd_iff_natAbs_dvd_natAbs]
    exact hd_b
  have h3 : Int.natAbs d ≤ Nat.gcd (Int.natAbs a) (Int.natAbs b) := by
    exact Nat.dvd_gcd_iff.mp ⟨h1, h2⟩
  rw [← Int.natAbs_of_nonneg (le_of_lt hd_pos)]
  exact Int.coe_nat_le_coe_nat_iff.mpr h3

-- LLM HELPER
lemma int_gcd_zero_zero : intGcd 0 0 = 0 := by
  unfold intGcd
  simp [Nat.gcd_zero_zero]

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec implementation
  let result := intGcd a b
  use result
  constructor
  · rfl
  · constructor
    · exact int_gcd_dvd_left a b
    · constructor
      · exact int_gcd_dvd_right a b
      · intros d' hd'_pos hd'_a hd'_b
        exact int_gcd_greatest a b d' hd'_pos hd'_a hd'_b