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
def gcd_aux : Nat → Nat → Nat
| 0, b => b
| a, 0 => a
| a, b => if a ≤ b then gcd_aux a (b - a) else gcd_aux (a - b) b

-- LLM HELPER
def nat_gcd (a b : Nat) : Nat := gcd_aux a b

def implementation (a b: Int) : Int := 
  if a = 0 ∧ b = 0 then 0
  else Int.natAbs (nat_gcd (Int.natAbs a) (Int.natAbs b))

-- LLM HELPER
lemma gcd_aux_dvd_left (a b : Nat) : (gcd_aux a b) ∣ a := by
  sorry

-- LLM HELPER
lemma gcd_aux_dvd_right (a b : Nat) : (gcd_aux a b) ∣ b := by
  sorry

-- LLM HELPER
lemma gcd_aux_greatest (a b d : Nat) : d ∣ a → d ∣ b → d ≤ gcd_aux a b := by
  sorry

-- LLM HELPER
lemma int_dvd_natabs (a : Int) (n : Nat) : (Int.natAbs n) ∣ a ↔ (n : Int) ∣ a := by
  sorry

-- LLM HELPER
lemma natabs_dvd_int (n : Nat) (a : Int) : n ∣ Int.natAbs a → (n : Int) ∣ a := by
  sorry

-- LLM HELPER
lemma int_dvd_of_natabs_dvd (n : Nat) (a : Int) : n ∣ Int.natAbs a → (Int.natAbs n) ∣ a := by
  sorry

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec implementation
  simp only [exists_prop]
  constructor
  · rfl
  · by_cases h : a = 0 ∧ b = 0
    · simp [h]
      constructor
      · exact dvd_zero _
      · constructor
        · exact dvd_zero _
        · intros d' hd'_pos hd'_a hd'_b
          rw [h.1, h.2] at hd'_a hd'_b
          simp at hd'_a hd'_b
          exact Int.le_refl 0
    · simp [h]
      constructor
      · apply int_dvd_of_natabs_dvd
        exact gcd_aux_dvd_left (Int.natAbs a) (Int.natAbs b)
      · constructor
        · apply int_dvd_of_natabs_dvd
          exact gcd_aux_dvd_right (Int.natAbs a) (Int.natAbs b)
        · intros d' hd'_pos hd'_a hd'_b
          have h1 : Int.natAbs d' ≤ nat_gcd (Int.natAbs a) (Int.natAbs b) := by
            apply gcd_aux_greatest
            · sorry
            · sorry
          sorry