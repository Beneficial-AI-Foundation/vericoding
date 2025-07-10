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
def gcd (a b: Int) : Int :=
if b = 0 then Int.natAbs a
else gcd b (a % b)
termination_by Int.natAbs b
decreasing_by simp_wf; exact Int.natAbs_mod_lt a (ne_of_gt (Int.natAbs_pos.mpr ‹b ≠ 0›))

def implementation (a b: Int) : Int := gcd a b

-- LLM HELPER
lemma gcd_dvd_left (a b: Int) : gcd a b ∣ a := by
  induction a, b using gcd.induction with
  | case1 a => 
    simp [gcd]
    exact Int.natAbs_dvd a
  | case2 a b hb ih =>
    simp [gcd, hb]
    have h := ih
    have : a = b * (a / b) + a % b := Int.emod_add_ediv a b
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left h _) h

-- LLM HELPER
lemma gcd_dvd_right (a b: Int) : gcd a b ∣ b := by
  induction a, b using gcd.induction with
  | case1 a => 
    simp [gcd]
    exact dvd_zero (Int.natAbs a)
  | case2 a b hb ih =>
    simp [gcd, hb]
    exact ih

-- LLM HELPER
lemma gcd_pos (a b: Int) : a ≠ 0 ∨ b ≠ 0 → gcd a b > 0 := by
  intro h
  induction a, b using gcd.induction with
  | case1 a => 
    simp [gcd]
    cases h with
    | inl ha => exact Int.natAbs_pos.mpr ha
    | inr hb => exact Int.natAbs_pos.mpr ha
  | case2 a b hb ih =>
    simp [gcd, hb]
    apply ih
    left
    exact hb

-- LLM HELPER
lemma gcd_greatest (a b d: Int) : d > 0 → d ∣ a → d ∣ b → d ≤ gcd a b := by
  induction a, b using gcd.induction with
  | case1 a => 
    intros hd hda hdb
    simp [gcd]
    have : d ≤ Int.natAbs a := by
      cases' Int.natAbs_eq a with h h
      · rw [h]
        exact Int.le_natAbs_of_nonneg_of_dvd (Int.of_nonneg_natAbs a) hda
      · rw [h]
        have : d ∣ -a := hda
        rw [dvd_neg] at this
        exact Int.le_natAbs_of_nonneg_of_dvd (Int.of_nonneg_natAbs a) this
    exact this
  | case2 a b hb ih =>
    intros hd hda hdb
    simp [gcd, hb]
    apply ih hd hdb
    have : a = b * (a / b) + a % b := Int.emod_add_ediv a b
    rw [this] at hda
    exact dvd_add_cancel_left (dvd_mul_of_dvd_left hdb _) hda

theorem correctness
(a b: Int)
: problem_spec implementation a b := by
  use gcd a b
  constructor
  · rfl
  · constructor
    · exact gcd_dvd_left a b
    · constructor
      · exact gcd_dvd_right a b
      · exact gcd_greatest a b