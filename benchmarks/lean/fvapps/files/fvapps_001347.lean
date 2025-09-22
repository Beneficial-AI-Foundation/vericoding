-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_distinct_subsequence (s : String) : Nat :=
  sorry

-- Property: output is always between 0 and length of input string
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (s : String) : 
  let result := longest_distinct_subsequence s
  0 ≤ result ∧ result ≤ s.length :=
sorry

-- Property: output equals number of unique characters 

theorem equals_unique_chars (s : String) :
  longest_distinct_subsequence s = s.toList.eraseDups.length :=
sorry

-- Property: result is at most size of alphabet used

theorem max_alphabet_size (s : String) :
  longest_distinct_subsequence s ≤ 26 :=
sorry

-- Property: empty string has 0 distinct chars

theorem empty_string :
  longest_distinct_subsequence "" = 0 :=
sorry

-- Property: string of repeated chars has length 1

theorem repeated_chars (c : Char) (n : Nat) :
  n > 0 → longest_distinct_subsequence (String.mk (List.replicate n c)) = 1 :=
sorry
-- </vc-theorems>