-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_url_anchor (s : String) : String := sorry 

theorem remove_url_anchor_splits_at_hash (base anchor : String) : 
  remove_url_anchor (base ++ "#" ++ anchor) = base := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_hash_in_result (s : String) : 
  ¬ (remove_url_anchor s).contains '#' := sorry

theorem no_hash_returns_same (s : String) : 
  ¬ s.contains '#' → remove_url_anchor s = s := sorry

theorem empty_string :
  remove_url_anchor "" = "" := sorry

theorem only_hash :
  remove_url_anchor "#" = "" := sorry

/-
info: 'www.codewars.com'
-/
-- #guard_msgs in
-- #eval remove_url_anchor "www.codewars.com#about"

/-
info: 'www.codewars.com/katas/?page=1'
-/
-- #guard_msgs in
-- #eval remove_url_anchor "www.codewars.com/katas/?page=1#about"

/-
info: 'www.codewars.com/katas/'
-/
-- #guard_msgs in
-- #eval remove_url_anchor "www.codewars.com/katas/"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded