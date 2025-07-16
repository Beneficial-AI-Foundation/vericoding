namespace NpGcd

def gcdInt (a b : Int) : Int := Int.gcd a b

/- LLM HELPER -/
lemma int_gcd_nonneg (a b : Int) : Int.gcd a b ≥ 0 := Int.gcd_nonneg a b

/- LLM HELPER -/
lemma dvd_iff_mod_eq_zero {a b : Int} : a ∣ b ↔ b % a = 0 := Int.dvd_iff_emod_eq_zero

theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  constructor
  · exact int_gcd_nonneg a b
  constructor
  · exact Int.dvd_iff_emod_eq_zero.mpr (Int.gcd_dvd_left a b)
  constructor
  · exact Int.dvd_iff_emod_eq_zero.mpr (Int.gcd_dvd_right a b)
  · intros d hd_pos ha hb
    have ha_dvd : d ∣ a := Int.dvd_iff_emod_eq_zero.mp ha
    have hb_dvd : d ∣ b := Int.dvd_iff_emod_eq_zero.mp hb
    exact Int.dvd_gcd ha_dvd hb_dvd

end NpGcd