/-
There are n oranges in the kitchen and you decided to eat some of these oranges every day as follows:

Eat one orange.
If the number of remaining oranges (n) is divisible by 2 then you can eat  n/2 oranges.
If the number of remaining oranges (n) is divisible by 3 then you can eat  2*(n/3) oranges.

You can only choose one of the actions per day.
Return the minimum number of days to eat n oranges.

Example 1:
Input: n = 10
Output: 4
Explanation: You have 10 oranges.
Day 1: Eat 1 orange,  10 - 1 = 9.  
Day 2: Eat 6 oranges, 9 - 2*(9/3) = 9 - 6 = 3. (Since 9 is divisible by 3)
Day 3: Eat 2 oranges, 3 - 2*(3/3) = 3 - 2 = 1. 
Day 4: Eat the last orange  1 - 1  = 0.
You need at least 4 days to eat the 10 oranges.

Example 2:
Input: n = 6
Output: 3
Explanation: You have 6 oranges.
Day 1: Eat 3 oranges, 6 - 6/2 = 6 - 3 = 3. (Since 6 is divisible by 2).
Day 2: Eat 2 oranges, 3 - 2*(3/3) = 3 - 2 = 1. (Since 3 is divisible by 3)
Day 3: Eat the last orange  1 - 1  = 0.
You need at least 3 days to eat the 6 oranges.

Example 3:
Input: n = 1
Output: 1

Example 4:
Input: n = 56
Output: 6

Constraints:

1 <= n <= 2*10^9
-/

-- <vc-helpers>
-- </vc-helpers>

def min_days_to_eat_oranges (n : Nat) : Nat := sorry 

theorem min_days_positive (n : Nat) (h : n > 0) (h₂ : n ≤ 10000) : 
  let result := min_days_to_eat_oranges n
  result ≥ 0 ∧ result ≤ n := sorry

theorem min_days_optimal_step (n : Nat) (h : n > 1) (h₂ : n ≤ 100) :
  min_days_to_eat_oranges n ≤ 1 + min 
    (n % 2 + min_days_to_eat_oranges (n / 2))
    (n % 3 + min_days_to_eat_oranges (n / 3)) := sorry

theorem min_days_base_cases :
  min_days_to_eat_oranges 0 = 0 ∧ 
  min_days_to_eat_oranges 1 = 1 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_days_to_eat_oranges 10

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_days_to_eat_oranges 6

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_days_to_eat_oranges 56

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible