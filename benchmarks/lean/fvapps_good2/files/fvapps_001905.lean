-- <vc-preamble>
def is_digit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_awesome_substring (s : String) : Nat := sorry

def string_reversal (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_length (s : String) (h : s.length > 0) (h2 : ∀ c ∈ s.data, is_digit c) :
  let result := longest_awesome_substring s
  1 ≤ result ∧ result ≤ s.length :=
sorry

theorem repeated_digit_awesome (d : Char) (n : Nat) (h : is_digit d) (h2 : n > 0) :
  let s := String.mk (List.replicate n d)
  longest_awesome_substring s = s.length :=
sorry

theorem palindrome_awesome (s : String) (h : s.length > 0) (h2 : ∀ c ∈ s.data, is_digit c) :
  let palindrome := s ++ string_reversal s
  longest_awesome_substring palindrome = palindrome.length :=
sorry

theorem single_odd_count_awesome (d1 d2 : Char) (h1 : is_digit d1) (h2 : is_digit d2) (h3 : d1 ≠ d2) :
  let s := String.mk (List.replicate 10 d1 ++ [d2])
  longest_awesome_substring s ≥ 11 :=
sorry

theorem reversal_invariant (s : String) (h : s.length > 0) (h2 : ∀ c ∈ s.data, is_digit c) :
  longest_awesome_substring s = longest_awesome_substring (string_reversal s) :=
sorry
-- </vc-theorems>