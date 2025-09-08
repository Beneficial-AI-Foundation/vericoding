/-
Philip's just turned four and he wants to know how old he will be in various years in the future such as 2090 or 3044. His parents can't keep up calculating this so they've begged you to help them out by writing a programme that can answer Philip's endless questions.

Your task is to write a function that takes two parameters: the year of birth and the year to count years in relation to. As Philip is getting more curious every day he may soon want to know how many years it was until he would be born, so your function needs to work with both dates in the future and in the past.

Provide output in this format: For dates in the future: "You are ... year(s) old." For dates in the past: "You will be born in ... year(s)." If the year of birth equals the year requested return: "You were born this very year!"

"..." are to be replaced by the number, followed and proceeded by a single space. Mind that you need to account for both "year" and "years", depending on the result.

Good Luck!
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_age (birth_year : Int) (current_year : Int) : String := sorry

theorem calculate_age_output_is_string (birth_year current_year : Int) :
  ∃ s : String, calculate_age birth_year current_year = s :=
sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded