-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_palindromic_substrings (s: String) : Nat :=
  sorry

def is_palindrome (s : String) : Bool :=
  sorry

def string_reverse (s : String) : String :=
  sorry

def string_repeat (c : Char) (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimum_palindromes (s : String) (h : s.length > 0) :
  count_palindromic_substrings s ≥ s.length :=
sorry

theorem empty_string :
  count_palindromic_substrings "" = 0 :=
sorry
-- </vc-theorems>