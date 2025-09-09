-- <vc-helpers>
-- </vc-helpers>

def checkValidString (s : String) : Bool := sorry

def isBalancedWithoutStars (s : String) : Bool := sorry

theorem check_matches_simple_validation (s : String) :
  (∀ c : Char, c ∈ s.data → (c = '(' ∨ c = ')')) →
  checkValidString s = isBalancedWithoutStars s := sorry

theorem empty_string_valid :
  checkValidString "" = true := sorry

theorem single_star_valid : 
  checkValidString "*" = true := sorry

theorem stars_to_empty_preserves_validity (s : String) :
  (checkValidString (s.replace "*" "") = true) → 
  checkValidString s = true := sorry

theorem close_exceeds_open_invalid (s : String) :
  (s.data.countP (· = ')')) > (s.data.countP (· = '(') + s.data.countP (· = '*')) →
  checkValidString s = false := sorry

theorem valid_parts_concat_with_stars_valid (parts : List String) :
  (∀ p ∈ parts, checkValidString p = true) →
  checkValidString (String.intercalate "*" parts) = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval check_valid_string "()"

/-
info: True
-/
-- #guard_msgs in
-- #eval check_valid_string "(*)"

/-
info: True
-/
-- #guard_msgs in
-- #eval check_valid_string "(*))"

-- Apps difficulty: interview
-- Assurance level: unguarded