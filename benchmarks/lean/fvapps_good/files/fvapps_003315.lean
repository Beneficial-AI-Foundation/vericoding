-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pigLatin (s : String) : String := sorry 

theorem pigLatin_word_transform {word : String} 
  (h : ∀ c ∈ word.data, c.isAlpha) : 
  word.length > 0 → 
  pigLatin word = (word.drop 1) ++ (word.take 1) ++ "ay" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pigLatin_word_count {text : String} :
  text.trim.length > 0 →
  ((pigLatin text).splitOn " ").length = (text.splitOn " ").length := sorry

theorem pigLatin_preserves_word_count {text : String} :
  text.length > 0 →
  text.trim.length > 0 →
  ((pigLatin text).splitOn " ").length = (text.splitOn " ").length := sorry

theorem pigLatin_word_list_transform {words : List String}
  (h : ∀ w ∈ words, ∀ c ∈ w.data, c.isAlpha) :
  words.length > 0 →
  (String.join words).splitOn " " = 
    words.map (λ w => (w.drop 1) ++ (w.take 1) ++ "ay") := sorry
-- </vc-theorems>