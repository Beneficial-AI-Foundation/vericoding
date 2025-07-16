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
  · exact Int.emod_gcd_left a b
  constructor
  · exact Int.emod_gcd_right a b
  · intros d hd_pos ha hb
    have ha_dvd : d ∣ a := Int.dvd_iff_emod_eq_zero.mpr ha
    have hb_dvd : d ∣ b := Int.dvd_iff_emod_eq_zero.mpr hb
    have h1 : Int.natAbs d ∣ Int.natAbs a := Int.natAbs_dvd_natAbs.mpr ha_dvd
    have h2 : Int.natAbs d ∣ Int.natAbs b := Int.natAbs_dvd_natAbs.mpr hb_dvd
    have h3 : Int.natAbs d ≤ Nat.gcd (Int.natAbs a) (Int.natAbs b) := Nat.le_gcd_of_dvd h1 h2
    have h4 : Int.gcd a b = Nat.gcd (Int.natAbs a) (Int.natAbs b) := Int.gcd_eq_natAbs a b
    have h5 : d = Int.natAbs d := Int.eq_natAbs_of_zero_le (le_of_lt hd_pos)
    rw [h5, h4]
    exact Int.coe_nat_le_coe_nat_iff.mpr h3

end NpGcd