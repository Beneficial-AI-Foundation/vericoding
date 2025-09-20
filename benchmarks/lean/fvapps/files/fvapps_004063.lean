-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) : Int := sorry

def isPrime (n : Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_closest_prime (n : Int) (h : n ≥ 2) : 
  let result := solve n
  isPrime result = true ∧ 
  ∀ i, isPrime i = true → (n - i).natAbs ≥ (n - result).natAbs := sorry

theorem solve_returns_input_if_prime (n : Int) (h1 : n ≥ 2) (h2 : isPrime n = true) : 
  solve n = n := sorry

theorem solve_handles_small_numbers (n : Int) (h : n ≤ 1) :
  solve n = 2 ∧ isPrime (solve n) = true := sorry
-- </vc-theorems>