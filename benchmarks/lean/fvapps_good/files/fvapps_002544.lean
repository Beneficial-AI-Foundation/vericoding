-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tv_remote (s : String) : Nat := sorry

theorem tv_remote_non_negative (word : String) : 
  tv_remote word ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tv_remote_greater_than_length (word : String) : 
  tv_remote word ≥ word.length := sorry 

theorem tv_remote_empty_zero : 
  tv_remote "" = 0 := sorry

theorem tv_remote_case_sensitive (word : String) : 
  (∃ c ∈ word.data, c.isAlpha) → 
  tv_remote (word.map Char.toUpper) ≠ tv_remote (word.map Char.toLower) := sorry

theorem tv_remote_spaces (spaces : String) : 
  (∀ c ∈ spaces.data, c = ' ') → 
  spaces.length > 0 → 
  tv_remote spaces ≥ spaces.length := sorry
-- </vc-theorems>