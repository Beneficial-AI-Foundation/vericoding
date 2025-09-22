-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_substring (main_str : String) (sub_str : String) : String := sorry

theorem is_substring_returns_y_or_n (main_str sub_str : String) :
  (is_substring main_str sub_str = "Y") ∨ (is_substring main_str sub_str = "N") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_is_substring (main_str : String) :
  is_substring main_str "" = "Y" := sorry

theorem string_is_substring_of_itself (str : String) :
  is_substring str str = "Y" := sorry 

theorem substring_result_matches_existence (main_str sub_str : String) :
  (is_substring main_str sub_str = "Y" ↔ ∃ a b : String, a ++ sub_str ++ b = main_str) := sorry

theorem substring_of_concatenation_left (s1 s2 : String) :
  is_substring (s1 ++ s2) s1 = "Y" := sorry

theorem substring_of_concatenation_right (s1 s2 : String) :
  is_substring (s1 ++ s2) s2 = "Y" := sorry
-- </vc-theorems>