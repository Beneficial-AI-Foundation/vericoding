-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_and_replace_pattern (words : List String) (pattern : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem word_length_matches_pattern (words : List String) (pattern : String) :
  ∀ w ∈ find_and_replace_pattern words pattern, String.length w = String.length pattern := by
  sorry

theorem result_subset_of_input (words : List String) (pattern : String) :
  ∀ w ∈ find_and_replace_pattern words pattern, w ∈ words := by
  sorry

theorem empty_input_returns_empty (pattern : String) :
  find_and_replace_pattern [] pattern = [] := by
  sorry

theorem identical_word_pattern_pair (pattern word : String) : 
  String.length word = String.length pattern →
  String.length (String.join (String.splitOn word "")) = 
  String.length (String.join (String.splitOn pattern "")) →
  word ∈ find_and_replace_pattern [word] word := by
  sorry

theorem pattern_mapping_consistency (pattern word : String) : 
  word ∈ find_and_replace_pattern [word] pattern →
  ∃ mapping : Char → Char,
  ∀ (i j : String.Pos), 
    (word.get i = word.get j ↔ pattern.get i = pattern.get j) := by
  sorry
-- </vc-theorems>