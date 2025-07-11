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

-- LLM HELPER
def int_gcd (a b: Int) : Int :=
Int.natAbs (gcd_helper (Int.natAbs a) (Int.natAbs b))

def implementation (a b: Int) : Int := int_gcd a b

-- LLM HELPER
lemma gcd_helper_dvd_left (a b: Nat) : (gcd_helper a b : Int) ∣ (a : Int) := by
  sorry

-- LLM HELPER
lemma gcd_helper_dvd_right (a b: Nat) : (gcd_helper a b : Int) ∣ (b : Int) := by
  sorry

-- LLM HELPER
lemma gcd_helper_greatest (a b: Nat) (d: Int) : d > 0 → d ∣ (a : Int) → d ∣ (b : Int) → d ≤ (gcd_helper a b : Int) := by
  sorry

-- LLM HELPER
lemma int_gcd_dvd_left (a b: Int) : int_gcd a b ∣ a := by
  unfold int_gcd
  have h1 : (gcd_helper (Int.natAbs a) (Int.natAbs b) : Int) ∣ (Int.natAbs a : Int) := gcd_helper_dvd_left (Int.natAbs a) (Int.natAbs b)
  have h2 : (Int.natAbs a : Int) = Int.natAbs a := rfl
  have h3 : Int.natAbs a = Int.natAbs a := rfl
  sorry

-- LLM HELPER
lemma int_gcd_dvd_right (a b: Int) : int_gcd a b ∣ b := by
  unfold int_gcd
  sorry

-- LLM HELPER
lemma int_gcd_greatest (a b: Int) (d: Int) : d > 0 → d ∣ a → d ∣ b → d ≤ int_gcd a b := by
  unfold int_gcd
  sorry

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