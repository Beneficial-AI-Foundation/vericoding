-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isMatch (s : String) (p : String) : Bool := sorry

theorem empty_pattern_empty_string (s : String) :
  isMatch s "" = (s = "") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_stars_match_everything (s p : String) (h : p ≠ "") (h2 : ∀ c ∈ p.data, c = '*') :
  isMatch s p = true := sorry

theorem single_char_pattern (s p : String) (h : p.length = 1) (h2 : p ≠ "*") (h3 : p ≠ "?") :
  isMatch s p = (s = p) := sorry

theorem star_repetition (s p : String) (h : '*' ∈ p.data) :
  isMatch s p = isMatch s (p.replace "*" "**") := sorry

theorem question_mark_same_length (s : String) :
  isMatch s (String.mk (List.replicate s.length '?')) = true := sorry

theorem question_mark_different_length (s : String) (h : s ≠ "") :
  isMatch s (String.mk (List.replicate (s.length - 1) '?')) = false ∧
  isMatch s (String.mk (List.replicate (s.length + 1) '?')) = false := sorry

theorem string_matches_itself (s : String) :
  isMatch s s = true := sorry

theorem string_matches_with_stars_between (s : String) (h : s ≠ "") :
  isMatch s (String.intercalate "*" (s.data.map toString)) = true := sorry

theorem edge_cases (s : String) :
  isMatch s "*" = true ∧
  isMatch s "**" = true ∧
  isMatch s "" = (s = "") := sorry
-- </vc-theorems>