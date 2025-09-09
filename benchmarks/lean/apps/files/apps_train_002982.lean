-- <vc-helpers>
-- </vc-helpers>

def people_with_age_drink (age : Int) : String := sorry

theorem kids_drink_toddy
  {age : Int}
  (h : age ≤ 13) :
  people_with_age_drink age = "drink toddy" := sorry

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

/-
info: 'drink toddy'
-/
-- #guard_msgs in
-- #eval people_with_age_drink 13

/-
info: 'drink coke'
-/
-- #guard_msgs in
-- #eval people_with_age_drink 17

/-
info: 'drink beer'
-/
-- #guard_msgs in
-- #eval people_with_age_drink 18

/-
info: 'drink beer'
-/
-- #guard_msgs in
-- #eval people_with_age_drink 20

/-
info: 'drink whisky'
-/
-- #guard_msgs in
-- #eval people_with_age_drink 21

-- Apps difficulty: introductory
-- Assurance level: unguarded