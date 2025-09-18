-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def inside_out_word (s : String) : String := sorry
def inside_out (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem inside_out_word_preserves_length (s : String) (h : s.length > 0) :
  (inside_out_word s).length = s.length := 
sorry

theorem inside_out_preserves_length (s : String) (h : s.length > 0) :
  (inside_out s).length = s.length :=
sorry

theorem space_positions_preserved (s : String) (h : s.length > 0) :
  ∀ pos : String.Pos, (s.get pos = ' ' ↔ (inside_out s).get pos = ' ') :=
sorry

theorem single_char_unchanged (s : String) (h : s.length = 1) :
  inside_out_word s = s ∧ inside_out s = s :=
sorry

theorem chars_preserved (s : String) (h : s.length > 0) :
  ∃ (perm : String.Pos → String.Pos),
    ∀ pos : String.Pos, (inside_out_word s).get pos = s.get (perm pos) :=
sorry
-- </vc-theorems>