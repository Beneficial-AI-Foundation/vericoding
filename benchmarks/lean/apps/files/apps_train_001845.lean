-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: [3, 3]
-/
-- #guard_msgs in
-- #eval closestDivisors 8

/-
info: [5, 25]
-/
-- #guard_msgs in
-- #eval closestDivisors 123

/-
info: sorted([25, 40])
-/
-- #guard_msgs in
-- #eval sorted closestDivisors(999)
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded