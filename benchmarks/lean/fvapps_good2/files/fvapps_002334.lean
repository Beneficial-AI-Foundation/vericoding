-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_palindrome_subseq (s : String) : Nat :=
sorry

def is_palindrome (s : String) : Bool :=
sorry

def reverse (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds (s : String) :
  0 ≤ remove_palindrome_subseq s ∧ remove_palindrome_subseq s ≤ 2 :=
sorry

theorem empty_string :
  remove_palindrome_subseq "" = 0 :=
sorry

theorem single_char_type (s : String) :
  s.length = 1 → remove_palindrome_subseq s = 1 :=
sorry

theorem only_valid_results (s : String) :
  remove_palindrome_subseq s = 0 ∨
  remove_palindrome_subseq s = 1 ∨
  remove_palindrome_subseq s = 2 :=
sorry
-- </vc-theorems>