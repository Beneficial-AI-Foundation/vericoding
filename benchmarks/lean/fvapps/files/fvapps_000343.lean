-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_str_chain (words : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_str_chain_non_negative 
  (words : List String) :
  longest_str_chain words ≥ 0 :=
sorry

theorem longest_str_chain_empty_list :
  longest_str_chain [] = 0 :=
sorry

theorem longest_str_chain_bounded_by_length
  (words : List String) :
  longest_str_chain words ≤ words.length :=
sorry

theorem longest_str_chain_singleton
  (word : String) :
  longest_str_chain [word] = 1 :=
sorry

theorem longest_str_chain_same_length_words
  (words : List String)
  (h : ∀ w ∈ words, w.length = 1) : 
  longest_str_chain words = 1 :=
sorry

theorem longest_str_chain_decreasing
  (word : String)
  (chain := List.range word.length |>.map (fun i => word.take (word.length - i))) :
  longest_str_chain chain = word.length ∨ longest_str_chain chain = 1 :=
sorry
-- </vc-theorems>