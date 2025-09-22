-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def word_pattern (pattern : String) (str: String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_length_match
  (pattern : String)
  (words : List String)
  (h : pattern.length ≠ words.length) :
  word_pattern pattern (String.intercalate " " words) = false :=
  sorry

theorem repeated_pattern
  (n : Nat) 
  (word : String)
  (h1 : n > 0)
  (h2 : n ≤ 10) :
  let pattern := String.mk (List.replicate n 'a')
  word_pattern pattern (String.intercalate " " (List.replicate n word)) = true :=
  sorry

theorem bijection  
  (pattern : String)
  (word1 word2 : String)
  (h1 : pattern.length ≥ 2)
  (h2 : pattern.length ≤ 10)
  (h3 : word1 ≠ word2) :
  let mapped := pattern.data.map (fun c => if c = pattern.data[0]! then word1 else word2)
  let uniquePatternChars := List.eraseDups pattern.data
  let uniqueMappedWords := List.eraseDups mapped
  word_pattern pattern (String.intercalate " " mapped) = 
  (uniquePatternChars.length = uniqueMappedWords.length) :=
  sorry
-- </vc-theorems>