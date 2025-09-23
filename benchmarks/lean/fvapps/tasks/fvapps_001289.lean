-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_days_to_eat_sweets (n : Nat) (sweets : List Nat) : Nat := sorry

theorem min_days_positive {n : Nat} {sweets : List Nat} :
  min_days_to_eat_sweets n sweets > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_days_upper_bound {n : Nat} {sweets : List Nat} :
  min_days_to_eat_sweets n sweets ≤ n := sorry

theorem min_days_lower_bound {n : Nat} {sweets : List Nat} :
  min_days_to_eat_sweets n sweets ≥ (n + 1) / 2 := sorry

theorem min_days_identical_sweets {n : Nat} {sweets : List Nat} :
  sweets.length = n →
  (∀ i j, i < sweets.length → j < sweets.length → sweets[i]! = sweets[j]!) →
  min_days_to_eat_sweets n sweets = (n + 1) / 2 := sorry

theorem min_days_all_different {n : Nat} {sweets : List Nat} :
  sweets.length = n →
  (∀ i j, i < sweets.length → j < sweets.length → i ≠ j → sweets[i]! ≠ sweets[j]!) →
  min_days_to_eat_sweets n sweets = n := sorry
-- </vc-theorems>