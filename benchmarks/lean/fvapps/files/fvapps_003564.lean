-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime (n : Nat) : Bool := sorry

def prime_product (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prime_positive_factors (n : Nat) (h : n ≥ 2) : 
  is_prime n = true → ∀ i : Nat, 2 ≤ i → i ≤ n^(1/2) → n % i ≠ 0 := sorry

theorem nonpositive_not_prime (n : Nat) :
  n ≤ 1 → is_prime n = false := sorry
-- </vc-theorems>