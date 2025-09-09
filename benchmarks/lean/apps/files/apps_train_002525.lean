-- <vc-helpers>
-- </vc-helpers>

def bird_code (names : List String) : List String := sorry

theorem empty_input_is_list : 
  ∀ (input : List String), 
  (input = [] ∨ input = [""] ∨ input = [" "]) →
  bird_code input = bird_code input := sorry

theorem specific_bird_codes :
  bird_code ["Black-Capped Chickadee"] = ["BCCH"] ∧
  bird_code ["Yellow-Rumped Warbler"] = ["YRWA"] ∧
  bird_code ["Common Tern"] = ["COTE"] ∧
  bird_code ["American Redstart"] = ["AMRE"] ∧
  bird_code ["Northern Cardinal"] = ["NOCA"] ∧
  bird_code ["Pine Grosbeak"] = ["PIGR"] := sorry

theorem multiple_names :
  bird_code ["Black-Capped Chickadee", "Common Tern", "American Redstart"] = 
  ["BCCH", "COTE", "AMRE"] := sorry

/-
info: ['BCCH', 'COTE']
-/
-- #guard_msgs in
-- #eval bird_code ["Black-Capped Chickadee", "Common Tern"]

/-
info: ['AMRE', 'NOCA', 'PIGR']
-/
-- #guard_msgs in
-- #eval bird_code ["American Redstart", "Northern Cardinal", "Pine Grosbeak"]

/-
info: ['GCFL', 'BOBO', 'ESOW']
-/
-- #guard_msgs in
-- #eval bird_code ["Great Crested Flycatcher", "Bobolink", "Eastern Screech Owl"]

-- Apps difficulty: introductory
-- Assurance level: unguarded