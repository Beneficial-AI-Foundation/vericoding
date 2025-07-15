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
  · exact Int.mod_gcd_eq_zero_left a b
  constructor
  · exact Int.mod_gcd_eq_zero_right a b
  · intros d hd_pos ha hb
    exact Int.le_gcd_of_dvd_of_dvd hd_pos (Int.dvd_iff_emod_eq_zero.mpr ha) (Int.dvd_iff_emod_eq_zero.mpr hb)

end NpGcd