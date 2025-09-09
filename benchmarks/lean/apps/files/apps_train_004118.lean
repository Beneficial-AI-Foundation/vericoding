-- <vc-helpers>
-- </vc-helpers>

def max_match (s : String) : List String :=
sorry

theorem max_match_empty (s : String) :
  s = "" → max_match s = [] :=
sorry

theorem max_match_happy_path1 (s : String) :
  s = "happyday" → max_match s = ["happy", "day"] :=
sorry

theorem max_match_happy_path2 (s : String) :
  s = "thecatsat" → max_match s = ["the", "cat", "sat"] :=
sorry

theorem max_match_edge_case (s : String) :
  s = "onthemat" → max_match s = ["on", "the", "mat"] :=
sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval max_match ""

/-
info: ['happy', 'day']
-/
-- #guard_msgs in
-- #eval max_match "happyday"

/-
info: ['the', 'cat', 'sat']
-/
-- #guard_msgs in
-- #eval max_match "thecatsat"

-- Apps difficulty: introductory
-- Assurance level: unguarded