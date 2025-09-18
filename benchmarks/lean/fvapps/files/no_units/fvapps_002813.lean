-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_drink_by_profession (profession : String) : String := sorry

def known_professions : List (String × String) := [
  ("jabroni", "Patron Tequila"),
  ("school counselor", "Anything with Alcohol"), 
  ("programmer", "Hipster Craft Beer"),
  ("bike gang member", "Moonshine"),
  ("politician", "Your tax dollars"),
  ("rapper", "Cristal")
]
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>