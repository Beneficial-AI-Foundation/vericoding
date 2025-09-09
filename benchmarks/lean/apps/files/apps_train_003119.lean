/-
_Friday 13th or Black Friday is considered as unlucky day. Calculate how many unlucky days are in the given year._

Find the number of Friday 13th in the given year.

__Input:__ Year as an integer.

__Output:__ Number of Black Fridays in the year as an integer.

__Examples:__

        unluckyDays(2015) == 3
        unluckyDays(1986) == 1

***Note:*** In Ruby years will start from 1593.
-/

-- <vc-helpers>
-- </vc-helpers>

def unlucky_days (year: Nat) : Nat := sorry

def is_friday_13th (year month: Nat) : Bool := sorry

theorem unlucky_days_bounds (year: Nat) (h: year ≥ 1583): 
  unlucky_days year ≤ 12 := sorry

theorem unlucky_days_nonneg (year: Nat) (h: year ≥ 1583):
  unlucky_days year ≥ 0 := sorry

theorem unlucky_days_400_year_cycle (year: Nat) (h: year ≥ 1583) (i: Nat):
  unlucky_days (year + i) = unlucky_days (year + i + 400) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval unlucky_days 2015

/-
info: 1
-/
-- #guard_msgs in
-- #eval unlucky_days 1986

/-
info: 2
-/
-- #guard_msgs in
-- #eval unlucky_days 1634

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible