-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def even_odd (n : Nat) : Nat × Nat := sorry
def is_prime (n : Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem even_odd_basic :
  even_odd 1 = (0, 1) ∧ even_odd 2 = (1, 1) := sorry

theorem even_odd_properties (n : Nat) (h : n > 0) :
  let (s, d) := even_odd n
  s ≥ 0 ∧ d % 2 = 1 ∧ n = d * (2 ^ s) := sorry

theorem is_prime_properties_one_and_less (n : Int) (h : n ≤ 1) :
  is_prime n = false := sorry

theorem is_prime_two :
  is_prime 2 = true := sorry

theorem is_prime_even (n : Int) (h1 : n > 2) (h2 : n % 2 = 0) :
  is_prime n = false := sorry

theorem is_prime_deterministic (n : Int) :
  is_prime n = is_prime n := sorry
-- </vc-theorems>