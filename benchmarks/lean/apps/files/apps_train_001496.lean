-- <vc-helpers>
-- </vc-helpers>

def classify_quotes (quote : String) : String := sorry

def splitString (s : String) : List String := sorry

theorem classify_quotes_result_valid (quote : String) :
  classify_quotes quote = "Real Fancy" ∨ classify_quotes quote = "regularly fancy" := sorry

theorem classify_quotes_not_condition (quote : String) :
  classify_quotes quote = (if (splitString quote).contains "not" then "Real Fancy" else "regularly fancy") := sorry

theorem classify_quotes_regular (quote : String) :
  ¬(splitString quote).contains "not" → classify_quotes quote = "regularly fancy" := sorry

theorem classify_quotes_all_not (n : Nat) (h : n > 0) :
  classify_quotes (String.join (List.replicate n "not" |>.intersperse " ")) = "Real Fancy" := sorry

/-
info: 'Real Fancy'
-/
-- #guard_msgs in
-- #eval classify_quotes "i do not have any fancy quotes"

/-
info: 'regularly fancy'
-/
-- #guard_msgs in
-- #eval classify_quotes "when nothing goes right go left"

/-
info: 'Real Fancy'
-/
-- #guard_msgs in
-- #eval classify_quotes "this is not fancy at all"

-- Apps difficulty: interview
-- Assurance level: unguarded