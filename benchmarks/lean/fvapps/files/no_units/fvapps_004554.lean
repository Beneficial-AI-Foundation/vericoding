-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_palindrome (s : String) : Bool := sorry

def String.reverse (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_single_char_palindrome (s : String) :
  s.length ≤ 1 → is_palindrome s := sorry 

theorem case_insensitive (s : String) :
  is_palindrome s = is_palindrome (s.toLower) ∧ 
  is_palindrome s = is_palindrome s.toUpper := sorry

theorem palindrome_reverse_property (s : String) :
  is_palindrome s = (s.toLower = (s.toLower).reverse) := sorry
-- </vc-theorems>