-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def my_very_own_split (s : String) (delimiter : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_matches_python_split (s : String) (delimiter : String) 
  (h : delimiter.length > 0) :
  my_very_own_split s delimiter = s.splitOn delimiter := 
  sorry

theorem split_empty_delimiter_raises (s : String) :
  delimiter.length = 0 → my_very_own_split s delimiter = [] := 
  sorry

theorem split_parts_recombine (s delimiter : String) 
  (h : delimiter.length > 0) 
  (parts := my_very_own_split s delimiter)
  (h2 : parts.length > 1) :
  String.intercalate delimiter parts = s :=
  sorry

theorem split_no_empty_middle_parts (s delimiter : String)
  (h : delimiter.length > 0) 
  (parts := my_very_own_split s delimiter)
  (middle_parts := parts.drop 1 |>.take (parts.length - 2)) :
  ∀ p ∈ middle_parts, p ≠ "" := 
  sorry
-- </vc-theorems>