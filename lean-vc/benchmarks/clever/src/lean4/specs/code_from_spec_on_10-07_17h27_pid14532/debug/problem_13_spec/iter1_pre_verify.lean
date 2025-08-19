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

def implementation (a b: Int) : Int := gcd_aux a b

-- LLM HELPER
lemma gcd_aux_dvd_left (a b : Int) : (gcd_aux a b : Int) ∣ a := by
  sorry

-- LLM HELPER
lemma gcd_aux_dvd_right (a b : Int) : (gcd_aux a b : Int) ∣ b := by
  sorry

-- LLM HELPER
lemma gcd_aux_pos (a b : Int) (ha : a ≠ 0 ∨ b ≠ 0) : (gcd_aux a b : Int) > 0 := by
  sorry

-- LLM HELPER
lemma gcd_aux_greatest (a b : Int) (d : Int) (hd_pos : d > 0) (hd_a : d ∣ a) (hd_b : d ∣ b) : d ≤ gcd_aux a b := by
  sorry

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