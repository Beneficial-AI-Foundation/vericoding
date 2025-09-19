-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime : Int → Bool := sorry
def next_prime : Int → Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_prime_larger (n : Int) :
  next_prime n > n := sorry

theorem next_prime_is_prime (n : Int) : 
  is_prime (next_prime n) = true := sorry

theorem no_primes_between (n : Int) :
  ∀ x, n < x → x < next_prime n → is_prime x = false := sorry

theorem prime_returns_self {n : Int} (h : n ≥ 2) (h2 : is_prime n = true) : 
  next_prime (n - 1) = n := sorry
-- </vc-theorems>