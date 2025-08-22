namespace NpGcd

def gcdInt (a b : Int) : Int := Int.gcd a b

/- LLM HELPER -/
lemma int_gcd_nonneg (a b : Int) : Int.gcd a b ≥ 0 := by
  exact Int.gcd_nonneg a b

/- LLM HELPER -/
lemma int_mod_gcd_eq_zero_left (a b : Int) : a % Int.gcd a b = 0 := by
  exact Int.emod_gcd_left a b

/- LLM HELPER -/
lemma int_mod_gcd_eq_zero_right (a b : Int) : b % Int.gcd a b = 0 := by
  exact Int.emod_gcd_right a b

theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  constructor
  · exact int_gcd_nonneg a b
  constructor
  · exact int_mod_gcd_eq_zero_left a b
  constructor
  · exact int_mod_gcd_eq_zero_right a b
  · intros d hd_pos ha hb
    have ha_dvd : d ∣ a := Int.dvd_iff_emod_eq_zero.mpr ha
    have hb_dvd : d ∣ b := Int.dvd_iff_emod_eq_zero.mpr hb
    exact Int.le_gcd_of_dvd ha_dvd hb_dvd (Int.natAbs_pos.mpr (ne_of_gt hd_pos))

end NpGcd