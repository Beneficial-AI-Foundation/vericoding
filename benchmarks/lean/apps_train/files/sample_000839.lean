/-
Recall the definition of the Fibonacci numbers:

f1 := 1

f2 := 2

fn := fn-1 + fn-2 (n>=3)

Given two numbers a and b, calculate how many Fibonacci numbers are in the range [a,b].

-----Input-----

The input contains several test cases. Each test case consists of two non-negative integer numbers a and b. Input is terminated by a=b=0. Otherwise, a<=b<=10^100. The numbers a and b are given with no superfluous leading zeros.

-----Output-----

For each test case output on a single line the number of Fibonacci numbers fi with a<=fi<=b.

-----Example-----
Input:

10 100
1234567890 9876543210
0 0

Output:

5
4
-/

-- <vc-helpers>
-- </vc-helpers>

def count_fibonacci_in_range (a b : Int) : Nat :=
  sorry

theorem zero_range_is_zero :
  count_fibonacci_in_range 0 0 = 0 :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_fibonacci_in_range 10 100

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_fibonacci_in_range 1234567890 9876543210

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_fibonacci_in_range 0 0

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible