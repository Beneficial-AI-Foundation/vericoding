/-
Write a function name `nextPerfectSquare` that returns the first perfect square that is greater than its integer argument. A `perfect square` is a integer that is equal to some integer squared. For example 16 is a perfect square because `16=4*4`. 
```
example

n   next perfect sqare

6    9
36   49 
0    1
-5   0 
```
```if-not:csharp
caution! the largest number tested is closer to `Number.MAX_SAFE_INTEGER`
```
```if:csharp
Caution! The largest number test is close to `Int64.MaxValue`
```
-/

-- <vc-helpers>
-- </vc-helpers>

def next_perfect_square (n: Int) : Int := sorry

theorem next_perfect_square_non_negative (n: Int) : 
  next_perfect_square n ≥ 0 := sorry

theorem next_perfect_square_negative_input (n: Int) : 
  n < 0 → next_perfect_square n = 0 := sorry

theorem next_perfect_square_is_perfect (n: Int) (h: n ≥ 0) :
  ∃ m: Int, next_perfect_square n = m * m := sorry

theorem next_perfect_square_greater_than_input (n: Int) (h: n ≥ 0) :
  next_perfect_square n > n := sorry

theorem next_perfect_square_is_smallest (n: Int) (h: n ≥ 0) :
  ∀ m: Int, m * m > next_perfect_square n → m * m > n := sorry

theorem next_perfect_square_of_perfect_square (n: Int) (h: n ≥ 0) :
  next_perfect_square (n * n) = (n + 1) * (n + 1) := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval next_perfect_square 6

/-
info: 49
-/
-- #guard_msgs in
-- #eval next_perfect_square 36

/-
info: 0
-/
-- #guard_msgs in
-- #eval next_perfect_square -5

-- Apps difficulty: introductory
-- Assurance level: unguarded