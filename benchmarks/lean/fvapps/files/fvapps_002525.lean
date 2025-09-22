-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bird_code (names : List String) : List String := sorry

theorem empty_input_is_list : 
  ∀ (input : List String), 
  (input = [] ∨ input = [""] ∨ input = [" "]) →
  bird_code input = bird_code input := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>