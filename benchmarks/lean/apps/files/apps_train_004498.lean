-- <vc-helpers>
-- </vc-helpers>

def GEESE : List String := ["African", "Roman Tufted", "Toulouse", "Pilgrim", "Steinbacher"]

def goose_filter (birds : List String) : List String := sorry

theorem output_is_subset {birds : List String} : 
  ∀ x ∈ goose_filter birds, x ∈ birds := sorry

theorem no_geese_in_output {birds : List String} :
  ∀ x ∈ goose_filter birds, x ∉ GEESE := sorry

theorem all_non_geese_preserved {birds : List String} :
  goose_filter birds = birds.filter (λ x => x ∉ GEESE) := sorry

/-
info: ['Mallard', 'Hook Bill', 'Crested', 'Blue Swedish']
-/
-- #guard_msgs in
-- #eval goose_filter ["Mallard", "Hook Bill", "African", "Crested", "Pilgrim", "Toulouse", "Blue Swedish"]

/-
info: ['Mallard', 'Barbary', 'Hook Bill', 'Blue Swedish', 'Crested']
-/
-- #guard_msgs in
-- #eval goose_filter ["Mallard", "Barbary", "Hook Bill", "Blue Swedish", "Crested"]

/-
info: []
-/
-- #guard_msgs in
-- #eval goose_filter ["African", "Roman Tufted", "Toulouse", "Pilgrim", "Steinbacher"]

-- Apps difficulty: introductory
-- Assurance level: unguarded