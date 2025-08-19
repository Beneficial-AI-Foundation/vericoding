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
def nat_gcd (a b : Nat) : Nat := 
  if b = 0 then a else nat_gcd b (a % b)

-- LLM HELPER
def int_gcd (a b : Int) : Int := 
  Int.natAbs (nat_gcd (Int.natAbs a) (Int.natAbs b))

def implementation (a b: Int) : Int := int_gcd a b

-- LLM HELPER
lemma nat_gcd_dvd_left (a b : Nat) : nat_gcd a b ∣ a := by
  induction b using Nat.strong_induction with
  | ind b ih =>
    unfold nat_gcd
    if h : b = 0 then
      simp [h]
    else
      simp [h]
      have : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
      have gcd_div_mod := ih (a % b) this
      have gcd_div_b := ih (a % b) this
      rw [Nat.dvd_iff_mod_eq_zero]
      sorry

-- LLM HELPER
lemma nat_gcd_dvd_right (a b : Nat) : nat_gcd a b ∣ b := by
  sorry

-- LLM HELPER
lemma int_gcd_dvd_left (a b : Int) : int_gcd a b ∣ a := by
  unfold int_gcd
  have h := nat_gcd_dvd_left (Int.natAbs a) (Int.natAbs b)
  rw [Int.dvd_iff_natAbs_dvd_natAbs]
  exact h

-- LLM HELPER
lemma int_gcd_dvd_right (a b : Int) : int_gcd a b ∣ b := by
  unfold int_gcd
  have h := nat_gcd_dvd_right (Int.natAbs a) (Int.natAbs b)
  rw [Int.dvd_iff_natAbs_dvd_natAbs]
  exact h

-- LLM HELPER
lemma int_gcd_greatest (a b d : Int) : d > 0 → d ∣ a → d ∣ b → d ≤ int_gcd a b := by
  intros h_pos h_div_a h_div_b
  unfold int_gcd
  have : Int.natAbs d ≤ nat_gcd (Int.natAbs a) (Int.natAbs b) := by
    sorry
  exact Int.coe_nat_le_coe_nat_iff.mpr this

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