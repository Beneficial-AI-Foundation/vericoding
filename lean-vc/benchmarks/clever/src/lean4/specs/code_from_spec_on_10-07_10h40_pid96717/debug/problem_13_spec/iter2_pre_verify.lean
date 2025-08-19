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
def natGcd (a b : Nat) : Nat := 
  if a = 0 then b
  else if b = 0 then a
  else if a ≤ b then natGcd a (b % a)
  else natGcd b (a % b)

-- LLM HELPER
def intGcd (a b : Int) : Int := Int.natAbs (natGcd (Int.natAbs a) (Int.natAbs b))

def implementation (a b: Int) : Int := intGcd a b

-- LLM HELPER
lemma natGcd_dvd_left (a b : Nat) : natGcd a b ∣ a := by
  unfold natGcd
  if h1 : a = 0 then
    simp [h1]
  else if h2 : b = 0 then
    simp [h2]
  else
    split_ifs with h3
    · have : b % a < a := Nat.mod_lt b (Nat.pos_of_ne_zero h1)
      have : natGcd a (b % a) ∣ a := by
        sorry -- induction would be needed here
      exact this
    · have : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h2)
      have : natGcd b (a % b) ∣ b := by
        sorry -- induction would be needed here
      have : natGcd b (a % b) ∣ a := by
        sorry -- induction would be needed here
      exact this

-- LLM HELPER
lemma natGcd_dvd_right (a b : Nat) : natGcd a b ∣ b := by
  sorry -- similar to above

-- LLM HELPER
lemma int_gcd_dvd_left (a b : Int) : intGcd a b ∣ a := by
  unfold intGcd
  rw [Int.dvd_iff_natAbs_dvd_natAbs]
  exact natGcd_dvd_left (Int.natAbs a) (Int.natAbs b)

-- LLM HELPER
lemma int_gcd_dvd_right (a b : Int) : intGcd a b ∣ b := by
  unfold intGcd
  rw [Int.dvd_iff_natAbs_dvd_natAbs]
  exact natGcd_dvd_right (Int.natAbs a) (Int.natAbs b)

-- LLM HELPER
lemma int_gcd_greatest (a b d : Int) (hd_pos : d > 0) (hd_a : d ∣ a) (hd_b : d ∣ b) : d ≤ intGcd a b := by
  unfold intGcd
  have h1 : Int.natAbs d ∣ Int.natAbs a := by
    rw [← Int.dvd_iff_natAbs_dvd_natAbs]
    exact hd_a
  have h2 : Int.natAbs d ∣ Int.natAbs b := by
    rw [← Int.dvd_iff_natAbs_dvd_natAbs]
    exact hd_b
  have h3 : Int.natAbs d ≤ natGcd (Int.natAbs a) (Int.natAbs b) := by
    sorry -- would need more lemmas about natGcd
  rw [← Int.natAbs_of_nonneg (le_of_lt hd_pos)]
  exact Int.coe_nat_le_coe_nat_iff.mpr h3

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