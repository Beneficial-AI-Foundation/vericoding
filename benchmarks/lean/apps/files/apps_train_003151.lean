/-
A strongness of an even number is the number of times we can successively divide by 2 until we reach an odd number starting with an even number n.

For example, if n = 12, then
* 12 / 2 = 6
* 6 / 2 = 3

So we divided successively 2 times and we reached 3, so the strongness of 12 is `2`.

If n = 16 then
* 16 / 2 = 8
* 8 / 2 = 4
* 4 / 2 = 2
* 2 / 2 = 1

we divided successively 4 times and we reached 1, so the strongness of 16 is `4`

# Task

Given a closed interval `[n, m]`, return the even number that is the strongest in the interval. If multiple solutions exist return the smallest strongest even number.

Note that programs must run within the allotted server time; a naive solution will probably time out.

# Constraints
```if-not:ruby
1 <= n < m <= INT_MAX
```
```if:ruby
1 <= n < m <= 2^64
```

# Examples
```
[1, 2]    -->   2  # 1 has strongness 0, 2 has strongness 1
[5, 10]   -->   8  # 5, 7, 9 have strongness 0; 6, 10 have strongness 1; 8 has strongness 3
[48, 56]  -->  48
-/

-- <vc-helpers>
-- </vc-helpers>

def is_power_of_two (n : Nat) : Bool := sorry 

def strongest_even (a b : Nat) : Nat := sorry

theorem power_of_two_cases (p : Nat) (h : p > 0 ∧ p ≤ 32) : 
  strongest_even (2^p - 1) (2^p + 1) = 2^p := sorry

theorem single_even_number (n : Nat) (h : n > 0) :
  strongest_even (2*n) (2*n) = 2*n := sorry

theorem small_range_properties (p : Nat) (h : p > 0 ∧ p ≤ 16) :
  strongest_even (2^p) (2^(p+1)) = 2^(p+1) := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval strongest_even 1 2

/-
info: 8
-/
-- #guard_msgs in
-- #eval strongest_even 5 10

/-
info: 48
-/
-- #guard_msgs in
-- #eval strongest_even 48 56

-- Apps difficulty: introductory
-- Assurance level: unguarded