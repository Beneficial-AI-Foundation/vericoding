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

/- LLM HELPER -/
lemma int_le_gcd_of_dvd (a b d : Int) (ha : d ∣ a) (hb : d ∣ b) (hd : d > 0) : d ≤ Int.gcd a b := by
  have h1 : Int.natAbs d ∣ Int.natAbs a := Int.natAbs_dvd_natAbs.mpr ha
  have h2 : Int.natAbs d ∣ Int.natAbs b := Int.natAbs_dvd_natAbs.mpr hb
  have h3 : Int.natAbs d ≤ Nat.gcd (Int.natAbs a) (Int.natAbs b) := Nat.le_gcd_of_dvd h1 h2
  have h4 : Int.gcd a b = Int.natAbs (Int.gcd a b) := Int.natAbs_of_nonneg (Int.gcd_nonneg a b)
  have h5 : Int.gcd a b = Nat.gcd (Int.natAbs a) (Int.natAbs b) := Int.gcd_eq_natAbs a b
  rw [h5] at h4
  have h6 : d = Int.natAbs d := Int.eq_natAbs_of_zero_le (le_of_lt hd)
  rw [h6, h4]
  exact Int.coe_nat_le_coe_nat_iff.mpr h3

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
    exact int_le_gcd_of_dvd a b d ha_dvd hb_dvd hd_pos

end NpGcd