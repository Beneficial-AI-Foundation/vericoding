-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_winner (s: String) : String := sorry 

theorem find_winner_valid_result (s: String) : 
  find_winner s = "SHANKY" ∨ find_winner s = "ANKU" ∨ find_winner s = "PANDEY" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_duplicates_returns_pandey {s: String} (h: s.length > 0) 
  (hdup: ∀ (i j : String.Pos), s.get i = s.get j) :
  find_winner s = "PANDEY" := sorry

theorem single_char_returns_pandey {s: String} (h: s.length = 1) :
  find_winner s = "PANDEY" := sorry

theorem two_chars_result {s: String} (h1: s.length ≥ 2)
  (h2: ∀ c ∈ s.data, 'a' = c ∨ 'b' = c) :
  (∀ (i j : String.Pos), s.get i = s.get j) →
    find_winner s = "PANDEY"
  ∧
  (∃ (i j : String.Pos), s.get i ≠ s.get j) →
    find_winner s = "SHANKY" ∨ find_winner s = "ANKU" ∨ find_winner s = "PANDEY" := sorry

theorem reverse_preserves_pandey {s: String} :
  find_winner s = "PANDEY" → find_winner (String.mk s.data.reverse) = "PANDEY" := sorry
-- </vc-theorems>