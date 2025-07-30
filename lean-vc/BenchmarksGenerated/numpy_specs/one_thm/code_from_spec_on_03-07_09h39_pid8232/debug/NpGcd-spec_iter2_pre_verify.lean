namespace NpGcd

def gcdInt (a b : Int) : Int := Int.gcd a b

theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  constructor
  · exact Int.gcd_nonneg a b
  constructor
  · exact Int.dvd_gcd_iff.mp (Int.gcd_dvd_left a b)
  constructor
  · exact Int.dvd_gcd_iff.mp (Int.gcd_dvd_right a b)
  · intros d hd_pos ha hb
    have ha_dvd : d ∣ a := Int.dvd_iff_mod_eq_zero.mpr ha
    have hb_dvd : d ∣ b := Int.dvd_iff_mod_eq_zero.mpr hb
    exact Int.dvd_gcd_iff.mp (Int.dvd_gcd ha_dvd hb_dvd)

end NpGcd