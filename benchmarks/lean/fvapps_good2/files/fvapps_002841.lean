-- <vc-preamble>
def countChar (c : Char) (s : String) : Nat :=
  (s.toList.filter (· = c)).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseAndCombineText (text : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input_chars (text : String) :
  String.length (reverseAndCombineText text) =
  String.length (String.replace text " " "") :=
sorry

theorem chars_preserved (text : String) (c : Char) :
  countChar c (String.replace text " " "") =
  countChar c (reverseAndCombineText text) :=
sorry

theorem halves_words_per_iteration (text : String) :
  let wordCount := (text.split (· = ' ')).length
  let maxIterations := if wordCount ≤ 1 then 0
                       else (wordCount - 1).log2 + 1
  ∀ result : String, result = reverseAndCombineText text →
  (result.split (· = ' ')).length ≤
    if wordCount ≤ 1 then 1 else wordCount / (2 ^ maxIterations) :=
sorry
-- </vc-theorems>