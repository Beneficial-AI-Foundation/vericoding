-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def StreamChecker.query : StreamChecker → String → Bool
  | _, _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_query_is_false (checker : StreamChecker) : 
  checker.query "" = false := by sorry

theorem matches_found_bounded_by_word_length (checker : StreamChecker) (words : List String) 
    (word : String) (h : word ∈ words) :
    ∀ stream : List Char,
    (stream.map (fun c => checker.query c.toString)).countP id ≤ word.length := by sorry

theorem binary_queries_bounded_results (checker : StreamChecker) (words : List String) 
    (h : words ≠ []) (maxlen : Nat) 
    (h_maxlen : maxlen = (List.map String.length words).foldl Nat.max 0) :
    ∀ stream : List Char,
    stream.length > maxlen + 1 →
    let results := stream.map (fun c => checker.query c.toString)
    (results.take maxlen).countP id ≤ 2 := by sorry

theorem duplicate_words_equivalent_behavior (words : List String) :
  ∀ c : String,
  (StreamChecker.mk words).query c = 
  (StreamChecker.mk (List.eraseDups words)).query c := by sorry
-- </vc-theorems>