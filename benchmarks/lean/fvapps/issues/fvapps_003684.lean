-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_smooth (n: Nat) : SmoothType := sorry

theorem is_smooth_valid_output (n: Nat) (h: n ≥ 2) : 
  is_smooth n = SmoothType.PowerOfTwo ∨ 
  is_smooth n = SmoothType.ThreeSmooth ∨
  is_smooth n = SmoothType.HammingNumber ∨ 
  is_smooth n = SmoothType.HumbleNumber ∨
  is_smooth n = SmoothType.NonSmooth := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem power_of_two (exp: Nat) (h: exp > 0) :
  is_smooth (2^exp) = SmoothType.PowerOfTwo := sorry

theorem product_of_two_and_three (exp2 exp3: Nat) (h1: exp2 > 0) (h2: exp3 > 0) :
  is_smooth ((2^exp2) * (3^exp3)) = SmoothType.ThreeSmooth := sorry

theorem hamming_numbers (exp2 exp3 exp5: Nat) 
  (h1: exp2 > 0) (h2: exp3 > 0) (h3: exp5 > 0) :
  is_smooth ((2^exp2) * (3^exp3) * (5^exp5)) = SmoothType.HammingNumber := sorry

theorem large_prime_factors (n: Nat) 
  (h1: n ≥ 13)
  (h2: ∃ p ∈ [11, 13, 17, 19, 23], n % p = 0) :
  is_smooth n = SmoothType.NonSmooth := sorry

/-
info: 'power of 2'
-/
-- #guard_msgs in
-- #eval is_smooth 16

/-
info: '3-smooth'
-/
-- #guard_msgs in
-- #eval is_smooth 36

/-
info: 'Hamming number'
-/
-- #guard_msgs in
-- #eval is_smooth 60
-- </vc-theorems>