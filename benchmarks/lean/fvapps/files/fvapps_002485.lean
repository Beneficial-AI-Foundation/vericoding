-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hyphenJoin (s : String) : String := sorry

theorem hyphen_join_word_count {words : List String} 
  (h1 : ∀ w ∈ words, w.length > 0) 
  (h2 : words.length > 0) :
  let input := String.join (List.intersperse " " words)
  let result := hyphenJoin input
  (result.splitOn "-").length = words.length ∧ 
  (result.splitOn "-") = words := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hyphen_join_whitespace_empty (s : String)
  (h : ∀ c ∈ s.data, c.isWhitespace) :
  hyphenJoin s = "" :=
sorry

theorem hyphen_join_basic_properties (s : String) 
  (h : s.length > 0) :
  let result := hyphenJoin s
  (¬ ∃ c ∈ result.data, c = ' ') ∧ 
  (s.trim ≠ "" → ((∃ c ∈ result.data, c = '-') ∨ (s.splitOn " ").length = 1)) :=
sorry
-- </vc-theorems>