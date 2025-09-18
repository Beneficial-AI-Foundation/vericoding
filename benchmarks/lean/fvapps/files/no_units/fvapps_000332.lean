-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth_ugly_number (n : Int) : Option Int := sorry

theorem nth_ugly_invalid_inputs {n : Int} (h : n ≤ 0) : 
  nth_ugly_number n = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nth_ugly_positive {n : Int} (h : n > 0) : 
  ∀ x, nth_ugly_number n = some x → x > 0 := sorry

theorem nth_ugly_prime_factors {n : Int} (h : n > 0) :
  ∀ x, nth_ugly_number n = some x → 
    ∃ a b c, x = 2^a * 3^b * 5^c := sorry

theorem nth_ugly_monotonic {n : Int} (h₁ : n > 1) :
  ∀ x y, nth_ugly_number n = some x → nth_ugly_number (n-1) = some y → 
    x > y := sorry

theorem nth_ugly_one : nth_ugly_number 1 = some 1 := sorry
-- </vc-theorems>