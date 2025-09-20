-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_palindrome (α : Type) [ToString α] (x : α) : Bool :=
  sorry

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
-- </vc-theorems>