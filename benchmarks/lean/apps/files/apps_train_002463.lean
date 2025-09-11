-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isLeap (year : Int) : Bool := sorry

theorem leap_year_400 (year : Int) (h : year > 0) (h400 : year % 400 = 0) : 
  isLeap year = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem leap_year_100 (year : Int) (h : year > 0) (h100 : year % 100 = 0) (h400 : year % 400 ≠ 0) :
  isLeap year = false := sorry

theorem leap_year_4 (year : Int) (h : year > 0) (h4 : year % 4 = 0) (h100 : year % 100 ≠ 0) :
  isLeap year = true := sorry

theorem non_leap_year (year : Int) (h : year > 0) (h4 : year % 4 ≠ 0) :
  isLeap year = false := sorry

theorem nonpositive_years (year : Int) (h : year ≤ 0) :
  isLeap year = true ∨ isLeap year = false := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_leap 1990

/-
info: True
-/
-- #guard_msgs in
-- #eval is_leap 2000

/-
info: False
-/
-- #guard_msgs in
-- #eval is_leap 1900
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded