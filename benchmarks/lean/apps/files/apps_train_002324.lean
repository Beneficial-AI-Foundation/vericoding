def is_palindrome (s : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def reverseString (s : String) : String :=
  sorry

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

/-
info: True
-/
-- #guard_msgs in
-- #eval is_palindrome "A man, a plan, a canal: Panama"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_palindrome "race a car"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_palindrome ""

-- Apps difficulty: introductory
-- Assurance level: unguarded