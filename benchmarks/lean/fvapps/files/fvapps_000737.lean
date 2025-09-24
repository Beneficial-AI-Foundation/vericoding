-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n : Nat) : Bool :=
  sorry

def find_min_potatoes (x y : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_potatoes_returns_prime_sum
  (x y : Nat) (h1 : x > 0) (h2 : y > 0) (h3 : x ≤ 1000) (h4 : y ≤ 1000) :
  let result := find_min_potatoes x y
  result ≥ 0 ∧ isPrime (x + y + result) = true := by
  sorry

theorem find_min_potatoes_with_equal_inputs
  (x : Nat) (h1 : x > 0) (h2 : x ≤ 1000) :
  let result := find_min_potatoes x x
  isPrime (2*x + result) = true := by
  sorry

theorem find_min_potatoes_reasonable_bounds
  (x y : Nat) (h1 : x > 0) (h2 : y > 0) (h3 : x ≤ 100) (h4 : y ≤ 100) :
  find_min_potatoes x y ≤ x + y := by
  sorry
-- </vc-theorems>