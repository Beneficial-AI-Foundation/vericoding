-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_chars_to_palindrome (s : String) : Nat := sorry

def count_char (s : String) (c : Char) : Nat := 
  s.data.filter (· = c) |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem min_chars_palindrome_non_negative (s : String) : 
  min_chars_to_palindrome s ≥ 0 := sorry

theorem empty_string_needs_no_changes :
  min_chars_to_palindrome "" = 0 := sorry

theorem single_char_needs_no_changes (c : Char) :
  min_chars_to_palindrome (String.mk [c]) = 0 := sorry

theorem result_bounded_by_length (s : String) :
  min_chars_to_palindrome s ≤ max (s.length - 1) 0 := sorry

theorem repeated_chars_palindrome (c : Char) (n : Nat) :
  min_chars_to_palindrome (String.mk (List.replicate n c)) = 0 := sorry
-- </vc-theorems>