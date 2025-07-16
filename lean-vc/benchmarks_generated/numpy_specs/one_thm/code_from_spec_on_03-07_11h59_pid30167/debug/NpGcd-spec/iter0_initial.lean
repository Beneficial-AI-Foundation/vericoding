namespace NpGcd

def gcdInt (a b : Int) : Int := Int.gcd a b

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
    exact Int.gcd_dvd_left a b
  constructor
  · -- b % gcdInt a b = 0
    unfold gcdInt
    exact Int.gcd_dvd_right a b
  · -- ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b
    intro d hd_pos ha_div hb_div
    unfold gcdInt
    exact Int.dvd_gcd_iff.mp ⟨ha_div, hb_div⟩

end NpGcd