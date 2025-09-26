-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def looseChange (cents : Int) : CoinChange := sorry

theorem loose_change_valid_values (cents : Int) :
  let result := looseChange cents
  result.quarters ≥ 0 ∧ 
  result.dimes ≥ 0 ∧
  result.nickels ≥ 0 ∧ 
  result.pennies ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem loose_change_optimal (cents : Int) (h : cents ≥ 0) (h2 : cents ≤ 1000) :
  let result := looseChange cents
  result.pennies < 5 ∧ 
  result.nickels < 2 ∧ 
  result.dimes < 3 ∧
  result.quarters * 25 + result.dimes * 10 + result.nickels * 5 + result.pennies = cents := sorry

/-
info: {'Nickels': 1, 'Pennies': 1, 'Dimes': 0, 'Quarters': 2}
-/
-- #guard_msgs in
-- #eval loose_change 56

/-
info: {'Nickels': 0, 'Pennies': 0, 'Dimes': 0, 'Quarters': 4}
-/
-- #guard_msgs in
-- #eval loose_change 100

/-
info: {'Nickels': 1, 'Pennies': 2, 'Dimes': 0, 'Quarters': 0}
-/
-- #guard_msgs in
-- #eval loose_change 7.9
-- </vc-theorems>