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
def nat_gcd (a b : Nat) : Nat := Nat.gcd a b

-- LLM HELPER
def int_gcd (a b : Int) : Int := Int.natAbs (nat_gcd (Int.natAbs a) (Int.natAbs b))

def implementation (a b: Int) : Int := int_gcd a b

-- LLM HELPER
lemma int_gcd_dvd_left (a b : Int) : int_gcd a b ∣ a := by
  unfold int_gcd
  have h := Nat.gcd_dvd_left (Int.natAbs a) (Int.natAbs b)
  rw [Int.dvd_iff_natAbs_dvd_natAbs]
  simp [Int.natAbs_of_nonneg]
  exact h

-- LLM HELPER
lemma int_gcd_dvd_right (a b : Int) : int_gcd a b ∣ b := by
  unfold int_gcd
  have h := Nat.gcd_dvd_right (Int.natAbs a) (Int.natAbs b)
  rw [Int.dvd_iff_natAbs_dvd_natAbs]
  simp [Int.natAbs_of_nonneg]
  exact h

-- LLM HELPER
lemma int_gcd_greatest (a b d : Int) : d > 0 → d ∣ a → d ∣ b → d ≤ int_gcd a b := by
  intros h_pos h_div_a h_div_b
  unfold int_gcd
  have h_nat_pos : 0 < Int.natAbs d := by
    rw [Int.natAbs_pos]
    exact ne_of_gt h_pos
  have h_div_a_nat : Int.natAbs d ∣ Int.natAbs a := by
    rw [← Int.dvd_iff_natAbs_dvd_natAbs]
    exact h_div_a
  have h_div_b_nat : Int.natAbs d ∣ Int.natAbs b := by
    rw [← Int.dvd_iff_natAbs_dvd_natAbs]
    exact h_div_b
  have h_le_nat := Nat.dvd_gcd_iff.mp ⟨h_div_a_nat, h_div_b_nat⟩
  have h_le_gcd : Int.natAbs d ≤ Nat.gcd (Int.natAbs a) (Int.natAbs b) := by
    exact Nat.le_gcd_of_dvd h_nat_pos h_div_a_nat h_div_b_nat
  rw [← Int.natAbs_of_nonneg (le_of_lt h_pos)]
  exact Int.coe_nat_le_coe_nat_iff.mpr h_le_gcd

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec
  simp [implementation]
  use int_gcd a b
  constructor
  · rfl
  · constructor
    · exact int_gcd_dvd_left a b
    · constructor
      · exact int_gcd_dvd_right a b
      · exact int_gcd_greatest a b