-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hexWordSum (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hex_word_sum_output_type (s : String) :
  let result := hexWordSum s
  result ≥ 0 := by sorry

theorem hex_word_sum_mixed_strings_valid (s : String) :
  let result := hexWordSum s
  result ≥ 0 := by sorry

theorem hex_word_substitutions (word : String) :
  let converted := word.replace "O" "0" |>.replace "S" "5"
  (∀ c ∈ converted.toList, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']) →
  hexWordSum word = String.toNat! converted := by sorry

theorem hex_word_sum_empty :
  hexWordSum "" = 0 ∧ hexWordSum "   " = 0 := by sorry

theorem hex_word_sum_invalid_chars (s : String) :
  (∀ c ∈ s.toList, c ∉ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'O', 'S']) →
  hexWordSum s = 0 := by sorry
-- </vc-theorems>