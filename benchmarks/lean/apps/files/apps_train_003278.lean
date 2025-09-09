-- <vc-helpers>
-- </vc-helpers>

def candies_to_buy (n : Nat) : Nat := sorry

theorem candies_to_buy_properties (n : Nat) (h : n > 0 ∧ n ≤ 20) : 
  let result := candies_to_buy n
  -- Result greater than or equal to n
  result ≥ n ∧ 
  -- Result evenly divisible by all numbers 1 to n
  (∀ i, 1 ≤ i ∧ i ≤ n → result % i = 0) ∧
  -- Result is positive
  result > 0 := sorry

theorem candies_to_buy_minimum : candies_to_buy 1 = 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval candies_to_buy 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval candies_to_buy 2

/-
info: 60
-/
-- #guard_msgs in
-- #eval candies_to_buy 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible