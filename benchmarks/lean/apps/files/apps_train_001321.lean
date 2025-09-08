/-
Chef Vivek is good in mathematics and likes solving problems on prime numbers. One day his friend Jatin told him about Victory numbers. Victory number can be defined as a number formed after summing up all the prime numbers till given number n. Now, chef Vivek who is very fond of solving questions on prime numbers got busy in some other tasks. Your task is to help him finding victory number.

-----Input:-----
- First line will contain $T$, number of test cases. Then the test cases follow. 
- Each test case contains of a single line of input $N$ till which sum of all prime numbers between 1 to n has to be calculated.

-----Output:-----
For each test case, output in a single line answer to the victory number.

-----Constraints-----
- $1 <= T <= 1000$
- $1 <= N <= 10^6$

-----Sample Input:-----
3
22
13
10

-----Sample Output:-----
77
41
17
-/

-- <vc-helpers>
-- </vc-helpers>

def find_victory_number (n : Nat) : Nat :=
  sorry

theorem victory_number_nonnegative (n : Nat) :
  n ≥ 1 → find_victory_number n ≥ 0 :=
  sorry

theorem victory_number_one :
  find_victory_number 1 = 0 :=
  sorry

theorem victory_number_two :
  find_victory_number 2 = 2 :=
  sorry

theorem victory_number_monotone (n : Nat) :
  n > 1 → find_victory_number n ≥ find_victory_number (n-1) :=
  sorry

theorem victory_number_contains_two (n : Nat) :
  n > 2 → find_victory_number n ≥ 2 :=
  sorry

/-
info: 77
-/
-- #guard_msgs in
-- #eval find_victory_number 22

/-
info: 41
-/
-- #guard_msgs in
-- #eval find_victory_number 13

/-
info: 17
-/
-- #guard_msgs in
-- #eval find_victory_number 10

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible