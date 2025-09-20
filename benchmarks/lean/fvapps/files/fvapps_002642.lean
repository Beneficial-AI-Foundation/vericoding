-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def likes (names : List String) : String := sorry

theorem likes_output_is_string (names : List String) : 
  ∃ s : String, likes names = s := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem likes_output_ends_correctly (names : List String) :
  (likes names).endsWith " likes this" ∨ (likes names).endsWith " like this" := by sorry

theorem likes_empty_case : 
  likes [] = "no one likes this" := by sorry

theorem likes_single_case (name : String) :
  likes [name] = name ++ " likes this" := by sorry

theorem likes_two_case (name1 name2 : String) :
  likes [name1, name2] = name1 ++ " and " ++ name2 ++ " like this" := by sorry

theorem likes_three_case (name1 name2 name3 : String) :
  likes [name1, name2, name3] = name1 ++ ", " ++ name2 ++ " and " ++ name3 ++ " like this" := by sorry

theorem likes_four_plus_case (names : List String) (h : names.length ≥ 4) :
  likes names = names[0]! ++ ", " ++ names[1]! ++ " and " ++ toString (names.length - 2) ++ " others like this" := by sorry

theorem likes_others_count_correct (names : List String) (h : names.length ≥ 4) :
  ∃ pre post : String, likes names = pre ++ toString (names.length - 2) ++ post := by sorry
-- </vc-theorems>