-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def processText (text : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_text_starts_ends_with_i (text : List String) (h : text.length > 0) : 
  let result := processText (String.intercalate " " text)
  result.take 1 = "I" ∧ result.takeRight 1 = "I" :=
  sorry

theorem process_text_i_count (text : List String) (h : text.length > 0) : 
  let result := processText (String.intercalate " " text)
  let iCount := String.length result - String.length (String.replace result "I" "")
  iCount = text.length + 1 :=
  sorry

theorem process_text_alternating_i (text : List String) (h : text.length > 0) :
  let result := processText (String.intercalate " " text)
  let words := String.split result (· = ' ')
  ∀ i, i < words.length → i % 2 = 0 → words[i]! = "I" :=
  sorry

theorem process_text_preserves_words (text : String) (h : text.length > 0) :
  let result := processText text
  let inputWords := String.split text (· = ' ') |>.filter (· ≠ "")
  let outputWords := String.split result (· = ' ') |>.filter (· ≠ "I")
  inputWords = outputWords :=
  sorry
-- </vc-theorems>