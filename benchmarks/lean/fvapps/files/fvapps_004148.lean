-- <vc-preamble>
def validPlanets : Int → Option String
| 1 => some "Mercury"
| 2 => some "Venus"
| 3 => some "Earth"
| 4 => some "Mars"
| 5 => some "Jupiter"
| 6 => some "Saturn"
| 7 => some "Uranus"
| 8 => some "Neptune"
| _ => none
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getPlanetName (id: Int) : Option String := sorry

theorem get_planet_name_matches_valid : ∀ (id : Int),
  getPlanetName id = validPlanets id := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_ids_return_none : ∀ (id : Int),
  (id < 1 ∨ id > 8) → getPlanetName id = none := by sorry

theorem valid_ids_return_some : ∀ (id : Int),
  (1 ≤ id ∧ id ≤ 8) → (∃ (name : String), getPlanetName id = some name) := by sorry

theorem valid_ids_match_planets : ∀ (id : Int),
  (1 ≤ id ∧ id ≤ 8) → getPlanetName id = validPlanets id := by sorry
-- </vc-theorems>