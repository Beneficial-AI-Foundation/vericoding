-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_palindrome (s : String) : Bool :=
  sorry

def reverseString (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_is_palindrome :
  is_palindrome "" = true :=
sorry

theorem string_plus_reverse_is_palindrome {s : String} :
  is_palindrome (s ++ reverseString s) = true :=
sorry

theorem case_insensitive {s : String} :
  is_palindrome s = is_palindrome (s.toUpper) ∧
  is_palindrome s = is_palindrome (s.toLower) :=
sorry

theorem punctuation_invariant {s p c : Char} :
  is_palindrome (String.mk [c]) = is_palindrome (String.mk [c, p]) :=
sorry

theorem single_char_is_palindrome {c : Char} :
  is_palindrome (String.mk [c]) = true :=
sorry
-- </vc-theorems>