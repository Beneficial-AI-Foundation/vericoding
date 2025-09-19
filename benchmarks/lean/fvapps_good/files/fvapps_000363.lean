-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isMatch (s : String) (p : String) : Bool := sorry 

@[simp]
-- </vc-definitions>

-- <vc-theorems>
theorem empty_pattern_matches_empty_string (s : String) : 
  isMatch s "" = !s.isEmpty = false := by sorry

@[simp]

theorem dot_star_matches_everything (s : String) : 
  isMatch s ".*" = true := by sorry 

@[simp]

theorem pattern_without_special_chars_exact_match (s p : String) 
  (h1 : ∀ c ∈ p.data, c ≠ '*' ∧ c ≠ '.') :
  isMatch s p = (s = p) := by sorry

@[simp]

theorem star_matches_zero_or_more (s : String) :
  isMatch s "a*" = (∀ c ∈ s.data, c = 'a') := by sorry

@[simp]

theorem self_matching (s : String) :
  isMatch s s = true := by sorry

@[simp]

theorem dots_match_same_length (s : String) :
  isMatch s (String.mk (List.replicate s.length '.')) = true := by sorry

@[simp]

theorem empty_string_cases_1 : isMatch "" "" = true := by sorry
@[simp]

theorem empty_string_cases_2 : isMatch "" "a*" = true := by sorry
@[simp] 

theorem empty_string_cases_3 : isMatch "a" "" = false := by sorry
-- </vc-theorems>