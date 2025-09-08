/-
In this Kata, you will be given a number and your task will be to rearrange the number so that it is divisible by `25`, but without leading zeros. Return the minimum number of digit moves that are needed to make this possible. If impossible, return `-1` ( `Nothing` in Haskell ).

For example:

More examples in test cases.

Good luck!
-/

-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) : Int := sorry

theorem solve_non_negative_or_minus_one (n : Nat) : 
  solve n ≥ -1 := sorry

theorem solve_impossible_single_digit (n : Nat) :
  n < 10 ∧ n % 5 ≠ 0 → solve n = -1 := sorry

theorem solve_leading_zeros (n m : Nat) :
  n = m → solve n = solve m := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve 50

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve 521

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve 7

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible