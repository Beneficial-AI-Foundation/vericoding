-- <vc-helpers>
-- </vc-helpers>

def how_many_years (date1 : String) (date2 : String) : Nat := sorry

theorem how_many_years_symmetric (date1 date2 : String) :
  how_many_years date1 date2 = how_many_years date2 date1 := sorry

theorem how_many_years_same_date (date : String) :
  how_many_years date date = 0 := sorry

theorem how_many_years_nonnegative (date1 date2 : String) :
  how_many_years date1 date2 ≥ 0 := sorry

/-
info: 18
-/
-- #guard_msgs in
-- #eval how_many_years "1997/10/10" "2015/10/10"

/-
info: 18
-/
-- #guard_msgs in
-- #eval how_many_years "2015/10/10" "1997/10/10"

/-
info: 0
-/
-- #guard_msgs in
-- #eval how_many_years "2000/01/01" "2000/01/01"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible