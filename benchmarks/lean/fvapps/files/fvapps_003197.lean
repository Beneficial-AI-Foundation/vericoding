-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def format_poem (s : String) : String := sorry

theorem format_poem_single_sentence (text : String) 
  (h : ¬ (text.contains '.' )) : 
  format_poem text = text ++ "." := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem format_poem_basic_sentences :
  format_poem "First sentence. Second sentence. Third sentence" = 
  "First sentence.\nSecond sentence.\nThird sentence." := sorry
-- </vc-theorems>