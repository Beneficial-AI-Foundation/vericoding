-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def group_cities (cities : List String) : List (List String) := sorry 

theorem group_cities_is_list_of_lists (cities : List String) :
  let result := group_cities cities
  ∀ group, group ∈ result → group = ([] : List String) ∨ group ≠ [] := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem group_cities_groups_sorted_by_size (cities : List String) :
  let result := group_cities cities
  ∀ i j, i < j → j < result.length → 
    (result.get ⟨i, by sorry⟩).length ≥ (result.get ⟨j, by sorry⟩).length := by sorry

theorem group_cities_groups_rotations :
  let result := group_cities ["Tokyo", "London", "Rome", "Donlon", "Kyoto"]
  (∃ group ∈ result, "Tokyo" ∈ group ∧ "Kyoto" ∈ group) ∧
  (∃ group ∈ result, "London" ∈ group ∧ "Donlon" ∈ group) := by sorry

theorem group_cities_empty :
  group_cities [] = [] := by sorry

theorem group_cities_duplicates :
  (group_cities ["Rome", "Rome", "Rome"]).length = 1 := by sorry
-- </vc-theorems>