-- <vc-preamble>
def remove_palindrome_subseq (s : String) : Nat := sorry

def is_palindrome (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse (s : String) : String := sorry

theorem result_bounds (s : String) :
  0 ≤ remove_palindrome_subseq s ∧ remove_palindrome_subseq s ≤ 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string :
  remove_palindrome_subseq "" = 0 := sorry

theorem single_char_type (s : String) :
  s.length = 1 → remove_palindrome_subseq s = 1 := sorry

theorem only_valid_results (s : String) :
  remove_palindrome_subseq s = 0 ∨ 
  remove_palindrome_subseq s = 1 ∨
  remove_palindrome_subseq s = 2 := sorry
-- </vc-theorems>