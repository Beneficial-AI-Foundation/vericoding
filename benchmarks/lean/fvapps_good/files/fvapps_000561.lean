-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_valid_subsequences (words: List String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input (words: List String) :
  List.length (count_valid_subsequences words) = List.length words :=
  sorry

theorem all_outputs_nonnegative (words: List String) :
  ∀ x ∈ count_valid_subsequences words, x ≥ 0 :=
  sorry

theorem no_a_gives_zero (words: List String) 
  (h: ∀ w ∈ words, ∀ c ∈ w.data, c ≠ 'a') :
  ∀ x ∈ count_valid_subsequences words, x = 0 :=
  sorry

theorem all_a_gives_maximum (words: List String)
  (h: ∀ w ∈ words, ∀ c ∈ w.data, c = 'a') :
  count_valid_subsequences words = words.map (fun w => 2^w.length - 1) :=
  sorry

theorem result_less_than_2_pow_n (words: List String) :
  ∀ (i: Nat), i < words.length → 
    (count_valid_subsequences words).get! i < 2^(words.get! i).length :=
  sorry
-- </vc-theorems>