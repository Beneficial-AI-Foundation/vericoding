-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_age (birth_year : Int) (current_year : Int) : String := sorry

theorem calculate_age_output_is_string (birth_year current_year : Int) :
  ∃ s : String, calculate_age birth_year current_year = s :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_age_same_year (year : Int) :
  calculate_age year year = "You were born this very year!" :=
sorry

theorem calculate_age_future (birth_year current_year : Int) :
  birth_year > current_year →
  calculate_age birth_year current_year = "You will be born in " ++ toString (birth_year - current_year) ++ (if birth_year - current_year ≠ 1 then "years." else "year.") :=
sorry

theorem calculate_age_past (birth_year current_year : Int) :
  birth_year < current_year →
  calculate_age birth_year current_year = "You are " ++ toString (current_year - birth_year) ++ (if current_year - birth_year ≠ 1 then " years old." else " year old.") :=
sorry

theorem calculate_age_pluralization_single (birth_year current_year : Int) :
  (current_year - birth_year).natAbs = 1 →
  (calculate_age birth_year current_year).data.indexOf 's' = 0 ∧
  (calculate_age birth_year current_year).data.contains 'r' :=
sorry

theorem calculate_age_pluralization_multiple (birth_year current_year : Int) :
  (current_year - birth_year).natAbs > 1 →
  (calculate_age birth_year current_year).data.contains 's' :=
sorry

/-
info: 'You are 4 years old.'
-/
-- #guard_msgs in
-- #eval calculate_age 2012 2016

/-
info: 'You will be born in 10 years.'
-/
-- #guard_msgs in
-- #eval calculate_age 2000 1990

/-
info: 'You were born this very year!'
-/
-- #guard_msgs in
-- #eval calculate_age 2000 2000
-- </vc-theorems>