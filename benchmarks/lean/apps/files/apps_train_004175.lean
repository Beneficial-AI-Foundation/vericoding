-- <vc-preamble>
def is_palindrome (α : Type) [ToString α] (x : α) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_palindrome_property (s : String) :
  is_palindrome String s = (s = reverse s) :=
  sorry

theorem integer_palindrome_property (n : Int) :
  is_palindrome Int n = (toString n = reverse (toString n)) :=
  sorry

theorem palindrome_type_invariant (s : String) :
  is_palindrome String s = is_palindrome String (toString s) :=
  sorry

theorem empty_string_is_palindrome :
  is_palindrome String "" = true :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_palindrome "anna"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_palindrome "walter"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_palindrome 12321
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded