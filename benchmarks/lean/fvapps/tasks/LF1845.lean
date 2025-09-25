-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def closestDivisors (n : Nat) : Nat × Nat := sorry

def find_divisors (n : Nat) : List (Nat × Nat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem closestDivisors_returns_valid_factors (n : Nat) (h : n > 0) :
  let result := closestDivisors n
  result.1 ≤ result.2 ∧ 
  (result.1 * result.2 = n + 1 ∨ result.1 * result.2 = n + 2) := sorry

theorem closestDivisors_finds_minimum_difference (n : Nat) (h : n > 0) :
  let result := closestDivisors n
  let diff := result.2 - result.1
  ∀ pair : Nat × Nat,
    pair ∈ find_divisors (n + 1) ∨ pair ∈ find_divisors (n + 2) →
    diff ≤ pair.2 - pair.1 := sorry
-- </vc-theorems>