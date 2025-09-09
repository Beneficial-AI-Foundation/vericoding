-- <vc-helpers>
-- </vc-helpers>

def yearDays (year : Int) : String := sorry

def isLeapYear (year : Int) : Bool := sorry

theorem yearDays_format {year : Int} : 
  yearDays year = s!"{year} has {if isLeapYear year then 366 else 365} days" := sorry

theorem yearDays_values {year : Int} :
  yearDays year = s!"{year} has 365 days" ∨ yearDays year = s!"{year} has 366 days" := sorry

theorem divisible_by_400_is_leap {year : Int} (h : year % 400 = 0) :
  yearDays year = s!"{year} has 366 days" := sorry

theorem divisible_by_4_not_100_is_leap {year : Int} (h1 : year % 4 = 0) (h2 : year % 100 ≠ 0) :
  yearDays year = s!"{year} has 366 days" := sorry

/-
info: '2000 has 366 days'
-/
-- #guard_msgs in
-- #eval year_days 2000

/-
info: '1974 has 365 days'
-/
-- #guard_msgs in
-- #eval year_days 1974

/-
info: '-64 has 366 days'
-/
-- #guard_msgs in
-- #eval year_days -64

-- Apps difficulty: introductory
-- Assurance level: unguarded