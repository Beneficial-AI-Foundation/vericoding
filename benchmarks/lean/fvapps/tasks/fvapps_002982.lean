-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def people_with_age_drink (age : Int) : String := sorry

theorem kids_drink_toddy
  {age : Int}
  (h : age ≤ 13) :
  people_with_age_drink age = "drink toddy" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem teens_drink_coke
  {age : Int}
  (h1 : age ≥ 14)
  (h2 : age ≤ 17) :
  people_with_age_drink age = "drink coke" := sorry

theorem young_adults_drink_beer
  {age : Int}
  (h1 : age ≥ 18)
  (h2 : age ≤ 20) :
  people_with_age_drink age = "drink beer" := sorry

theorem adults_drink_whisky
  {age : Int}
  (h : age ≥ 21) :
  people_with_age_drink age = "drink whisky" := sorry
-- </vc-theorems>