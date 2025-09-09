/-
Write a program to obtain a number $N$ and increment its value by 1 if the number is divisible by 4 $otherwise$ decrement its value by 1.

-----Input:-----
- First line will contain a number $N$.

-----Output:-----
Output a single line, the new value of the number.

-----Constraints-----
- $0 \leq N \leq 1000$

-----Sample Input:-----
5

-----Sample Output:-----
4

-----EXPLANATION:-----
Since 5 is not divisible by 4 hence, its value is decreased by 1.
-/

-- <vc-helpers>
-- </vc-helpers>

def increment_or_decrement (n : Int) : Int := sorry

theorem increment_or_decrement_divisible_by_4 (n : Int) : 
  n % 4 = 0 → increment_or_decrement n = n + 1 := sorry

theorem increment_or_decrement_not_divisible_by_4 (n : Int) :
  n % 4 ≠ 0 → increment_or_decrement n = n - 1 := sorry

theorem increment_or_decrement_distance (n : Int) :
  (increment_or_decrement n - n = 1) ∨ (increment_or_decrement n - n = -1) := sorry 

theorem increment_or_decrement_not_idempotent (n : Int) :
  increment_or_decrement (increment_or_decrement n) ≠ increment_or_decrement n := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval increment_or_decrement 5

/-
info: 9
-/
-- #guard_msgs in
-- #eval increment_or_decrement 8

/-
info: 2
-/
-- #guard_msgs in
-- #eval increment_or_decrement 3

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible