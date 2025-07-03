namespace NpGcd

def gcdInt (a b : Int) : Int := Int.natAbs (Int.gcd a b)

/- LLM HELPER -/
lemma int_gcd_nonneg (a b : Int) : Int.gcd a b ≥ 0 := by
  rw [Int.gcd_eq_natAbs]
  exact Int.natAbs_nonneg _

/- LLM HELPER -/
lemma int_emod_gcd_left (a b : Int) : a % Int.gcd a b = 0 := by
  rw [Int.gcd_eq_natAbs]
  exact Int.emod_natAbs_gcd_left a b

/- LLM HELPER -/
lemma int_emod_gcd_right (a b : Int) : b % Int.gcd a b = 0 := by
  rw [Int.gcd_eq_natAbs]
  exact Int.emod_natAbs_gcd_right a b

/- LLM HELPER -/
lemma nat_le_gcd_of_dvd {a b d : Nat} (ha : d ∣ a) (hb : d ∣ b) : d ≤ Nat.gcd a b := by
  exact Nat.dvd_gcd_iff.mp ⟨ha, hb⟩

/- LLM HELPER -/
lemma int_gcd_eq_natabs (a b : Int) : Int.gcd a b = Int.natAbs (Nat.gcd (Int.natAbs a) (Int.natAbs b)) := by
  rw [Int.gcd_eq_natAbs]
  simp

theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b := by
  constructor
  · simp [gcdInt]
    exact Int.natAbs_nonneg _
  constructor
  · simp [gcdInt]
    exact Int.emod_natAbs_gcd_left a b
  constructor
  · simp [gcdInt]
    exact Int.emod_natAbs_gcd_right a b
  · intros d hd_pos ha hb
    have ha_dvd : d ∣ a := Int.dvd_iff_emod_eq_zero.mpr ha
    have hb_dvd : d ∣ b := Int.dvd_iff_emod_eq_zero.mpr hb
    have h1 : Int.natAbs d ∣ Int.natAbs a := Int.natAbs_dvd_natAbs.mpr ha_dvd
    have h2 : Int.natAbs d ∣ Int.natAbs b := Int.natAbs_dvd_natAbs.mpr hb_dvd
    have h3 : Int.natAbs d ≤ Nat.gcd (Int.natAbs a) (Int.natAbs b) := Nat.le_gcd_of_dvd h1 h2
    have h5 : d = Int.natAbs d := Int.eq_natAbs_of_nonneg (Int.le_of_lt hd_pos)
    rw [h5, gcdInt]
    simp [Int.gcd_eq_natAbs]
    exact Int.coe_nat_le_coe_nat_iff.mpr h3

end NpGcd