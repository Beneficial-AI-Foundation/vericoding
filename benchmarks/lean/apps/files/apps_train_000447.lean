/-
You are given coins of different denominations and a total amount of money amount. Write a function to compute the fewest number of coins that you need to make up that amount. If that amount of money cannot be made up by any combination of the coins, return -1.
You may assume that you have an infinite number of each kind of coin.

Example 1:
Input: coins = [1,2,5], amount = 11
Output: 3
Explanation: 11 = 5 + 5 + 1

Example 2:
Input: coins = [2], amount = 3
Output: -1

Example 3:
Input: coins = [1], amount = 0
Output: 0

Example 4:
Input: coins = [1], amount = 1
Output: 1

Example 5:
Input: coins = [1], amount = 2
Output: 2

Constraints:

1 <= coins.length <= 12
1 <= coins[i] <= 231 - 1
0 <= amount <= 104
-/

-- <vc-helpers>
-- </vc-helpers>

def coin_change (coins : List Nat) (amount : Nat) : Int := sorry

def list_min : List Nat → Nat 
| [] => 0
| [x] => x
| (x::xs) => Nat.min x (list_min xs)

theorem coin_change_valid_output {coins : List Nat} {amount : Nat}
  (h1 : coins.length > 0)
  (h2 : ∀ x ∈ coins, x > 0 ∧ x ≤ 20) :
  let result := coin_change coins amount
  result ≥ -1 ∧ (result ≠ -1 → result ≤ amount) := sorry

theorem coin_change_zero_amount {coins : List Nat}
  (h1 : coins.length > 0)
  (h2 : ∀ x ∈ coins, x > 0 ∧ x ≤ 20) :
  coin_change coins 0 = 0 := sorry

theorem coin_change_impossible_amount {coins : List Nat}
  (h1 : coins.length > 0)
  (h2 : ∀ x ∈ coins, x ≥ 2 ∧ x ≤ 20) :
  coin_change coins 1 = -1 := sorry

theorem coin_change_min_coin {coins : List Nat}
  (h1 : coins.length > 0)
  (h2 : ∀ x ∈ coins, x > 0 ∧ x ≤ 20)
  (h3 : list_min coins > 1) :
  coin_change coins (list_min coins - 1) = -1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval coin_change [1, 2, 5] 11

/-
info: -1
-/
-- #guard_msgs in
-- #eval coin_change [2] 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval coin_change [1] 0

-- Apps difficulty: interview
-- Assurance level: unguarded