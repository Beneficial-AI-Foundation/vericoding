-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkValidString (s : String) : Bool := sorry

def isBalancedWithoutStars (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>