-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def anagram_counter (words : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem anagram_counter_properties (words : List String) :
  let result := anagram_counter words
  let n := words.length
  let max_pairs := n * (n-1) / 2
  result ≥ 0 ∧ result ≤ max_pairs := by sorry

theorem identical_words_property (word : String) (n : Nat) :
  let words := List.replicate n word
  let expected := n * (n-1) / 2
  anagram_counter words = expected := by sorry

theorem empty_list_property :
  anagram_counter [] = 0 := by sorry
-- </vc-theorems>