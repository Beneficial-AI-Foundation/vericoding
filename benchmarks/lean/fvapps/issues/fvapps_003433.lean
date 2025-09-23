-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_zodiac_sign (day : Nat) (month : Nat) : ZodiacSign := sorry

theorem zodiac_sign_january_ranges (day : Nat) (h1 : 1 ≤ day) (h2 : day ≤ 31) :
  day ≤ 19 → get_zodiac_sign day 1 = ZodiacSign.Capricorn ∧
  day ≥ 20 → get_zodiac_sign day 1 = ZodiacSign.Aquarius := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zodiac_sign_year_boundaries :
  get_zodiac_sign 1 1 = ZodiacSign.Capricorn ∧ 
  get_zodiac_sign 31 12 = ZodiacSign.Capricorn := sorry

theorem zodiac_sign_february_special :
  get_zodiac_sign 19 2 = ZodiacSign.Pisces := sorry

theorem zodiac_sign_valid_days (month : Nat) (day : Nat)
  (h1 : 1 ≤ month) (h2 : month ≤ 12) (h3 : 1 ≤ day) :
  (month ∈ [4,6,9,11] → day ≤ 30) →
  (month = 2 → day ≤ 29) →
  (month ∉ [2,4,6,9,11] → day ≤ 31) → 
  ∃ sign : ZodiacSign, get_zodiac_sign day month = sign := sorry

/-
info: 'Libra'
-/
-- #guard_msgs in
-- #eval get_zodiac_sign 10 10

/-
info: 'Taurus'
-/
-- #guard_msgs in
-- #eval get_zodiac_sign 1 5

/-
info: 'Sagittarius'
-/
-- #guard_msgs in
-- #eval get_zodiac_sign 25 11
-- </vc-theorems>