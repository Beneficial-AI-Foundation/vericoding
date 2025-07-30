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
  · exact Int.mod_gcd_left a b
  constructor
  · exact Int.mod_gcd_right a b
  · intros d hd_pos ha hb
    exact Int.gcd_greatest_right d a b ha hb hd_pos

end NpGcd