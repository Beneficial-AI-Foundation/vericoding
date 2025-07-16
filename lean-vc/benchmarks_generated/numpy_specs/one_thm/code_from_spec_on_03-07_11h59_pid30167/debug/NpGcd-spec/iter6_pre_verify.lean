namespace NpGcd

def gcdInt (a b : Int) : Int := Int.gcd a b

/- LLM HELPER -/
lemma int_gcd_nonneg (a b : Int) : Int.gcd a b ≥ 0 := by
  exact Int.gcd_nonneg a b

/- LLM HELPER -/
lemma dvd_iff_mod_eq_zero (a d : Int) : (d ∣ a) ↔ (a % d = 0) := by
  exact Int.dvd_iff_emod_eq_zero

/- LLM HELPER -/
lemma int_gcd_dvd_of_dvd_both (a b d : Int) : d ∣ a → d ∣ b → d ∣ Int.gcd a b := by
  exact Int.dvd_gcd

/- LLM HELPER -/
lemma int_dvd_le_of_pos_dvd (a d : Int) : d > 0 → d ∣ a → a ≠ 0 → d ≤ Int.natAbs a := by
  intro hd_pos hdvd ha_ne_zero
  exact Int.dvd_natAbs.mp hdvd

theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  constructor
  · -- gcdInt a b ≥ 0
    unfold gcdInt
    exact Int.gcd_nonneg a b
  constructor
  · -- a % gcdInt a b = 0
    unfold gcdInt
    exact Int.dvd_iff_emod_eq_zero.mp (Int.gcd_dvd_left a b)
  constructor
  · -- b % gcdInt a b = 0
    unfold gcdInt
    exact Int.dvd_iff_emod_eq_zero.mp (Int.gcd_dvd_right a b)
  · -- ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b
    intro d hd_pos ha_div hb_div
    unfold gcdInt
    have ha_dvd : d ∣ a := Int.dvd_iff_emod_eq_zero.mpr ha_div
    have hb_dvd : d ∣ b := Int.dvd_iff_emod_eq_zero.mpr hb_div
    have hgcd_dvd : d ∣ Int.gcd a b := Int.dvd_gcd ha_dvd hb_dvd
    exact Int.le_gcd_of_dvd hd_pos hgcd_dvd

end NpGcd