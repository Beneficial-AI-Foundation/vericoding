-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_leap_year (year : Nat) : Bool := sorry

theorem leap_year_div_400 (year : Nat) (h : year > 0) (h2 : year % 400 = 0) :
  is_leap_year year = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_leap_year_div_100_not_400 (year : Nat) (h : year > 0) 
    (h2 : year % 100 = 0) (h3 : year % 400 ≠ 0) :
  is_leap_year year = false := sorry

theorem leap_year_div_4_not_100 (year : Nat) (h : year > 0)
    (h2 : year % 4 = 0) (h3 : year % 100 ≠ 0) :
  is_leap_year year = true := sorry

theorem non_leap_year_others (year : Nat) (h : year > 0)
    (h2 : year % 4 ≠ 0) :
  is_leap_year year = false := sorry

theorem four_year_cycle (year : Nat) (h : year > 0) (h2 : year % 100 ≠ 0) :
  let next_leap := year + (4 - year % 4)
  is_leap_year next_leap = true ∧ next_leap % 4 = 0 := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_leap_year 1984

/-
info: True
-/
-- #guard_msgs in
-- #eval is_leap_year 2000

/-
info: False
-/
-- #guard_msgs in
-- #eval is_leap_year 1234
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded