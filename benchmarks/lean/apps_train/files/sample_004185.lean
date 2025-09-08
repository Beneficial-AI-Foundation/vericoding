/-
Welcome young Jedi! In this Kata you must create a function that takes an amount of US currency in `cents`, and returns a dictionary/hash which shows the least amount of coins used to make up that amount. The only coin denominations considered in this exercise are: `Pennies (1¢), Nickels (5¢), Dimes (10¢) and Quarters (25¢)`.
Therefor the dictionary returned should contain exactly 4 key/value pairs.

Notes:

* If the function is passed either 0 or a negative number, the function should return the dictionary with all values equal to 0.
* If a float is passed into the function, its value should be be rounded down, and the resulting dictionary should never contain fractions of a coin.

## Examples
```
loose_change(56)    ==>  {'Nickels': 1, 'Pennies': 1, 'Dimes': 0, 'Quarters': 2}
loose_change(-435)  ==>  {'Nickels': 0, 'Pennies': 0, 'Dimes': 0, 'Quarters': 0}
loose_change(4.935) ==>  {'Nickels': 0, 'Pennies': 4, 'Dimes': 0, 'Quarters': 0}
```
-/

-- <vc-helpers>
-- </vc-helpers>

def looseChange (cents : Int) : CoinChange := sorry

theorem loose_change_valid_values (cents : Int) :
  let result := looseChange cents
  result.quarters ≥ 0 ∧ 
  result.dimes ≥ 0 ∧
  result.nickels ≥ 0 ∧ 
  result.pennies ≥ 0 := sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded