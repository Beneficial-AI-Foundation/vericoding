/-
Write a function `getDrinkByProfession`/`get_drink_by_profession()` that receives as input parameter a string, and produces outputs according to the following table:

Input
Output

"Jabroni"
"Patron Tequila"

"School Counselor"
"Anything with Alcohol"

 "Programmer"
 "Hipster Craft Beer"

 "Bike Gang Member"
"Moonshine" 

 "Politician"
"Your tax dollars" 

 "Rapper"
"Cristal" 

 *anything else* 
"Beer" 

Note: *anything else* is the default case: if the input to the function is not any of the values in the table, then the return value should be "Beer."

Make sure you cover the cases where certain words do not show up with correct capitalization. For example, getDrinkByProfession("pOLitiCIaN") should still return "Your tax dollars".
-/

-- <vc-helpers>
-- </vc-helpers>

def get_drink_by_profession (profession : String) : String := sorry

def known_professions : List (String × String) := [
  ("jabroni", "Patron Tequila"),
  ("school counselor", "Anything with Alcohol"), 
  ("programmer", "Hipster Craft Beer"),
  ("bike gang member", "Moonshine"),
  ("politician", "Your tax dollars"),
  ("rapper", "Cristal")
]

theorem known_profession_case_insensitive 
  (profession : String)
  (h : profession.toLower ∈ (known_professions.map Prod.fst).map String.toLower) :
  ∃ drink, (get_drink_by_profession profession = drink ∧ 
           (profession.toLower, drink) ∈ (known_professions.map (fun p => (p.1.toLower, p.2)))) := 
sorry

theorem unknown_profession_returns_beer
  (profession : String) 
  (h : profession.toLower ∉ (known_professions.map Prod.fst).map String.toLower) :
  get_drink_by_profession profession = "Beer" :=
sorry

theorem exact_match_returns_correct_drink
  (profession : String)
  (h : profession ∈ known_professions.map Prod.fst) :
  ∃ drink, (get_drink_by_profession profession = drink ∧
           (profession, drink) ∈ known_professions) :=
sorry

/-
info: 'Patron Tequila'
-/
-- #guard_msgs in
-- #eval get_drink_by_profession "jabrOni"

/-
info: 'Your tax dollars'
-/
-- #guard_msgs in
-- #eval get_drink_by_profession "pOLiTiCIaN"

/-
info: 'Beer'
-/
-- #guard_msgs in
-- #eval get_drink_by_profession "pundit"

-- Apps difficulty: introductory
-- Assurance level: unguarded