-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.isPalindrome (s : String) : Bool :=
sorry

def find_longest_palindrome (s : String) : String :=
sorry

def String.isSubstringOf (sub str : String) : Bool :=
sorry

def String.substring (str : String) (start len : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_longest_palindrome_is_substring (s : String) :
  (find_longest_palindrome s).isSubstringOf s = true :=
sorry

theorem find_longest_palindrome_is_palindrome (s : String) :
  (find_longest_palindrome s).isPalindrome = true :=
sorry

theorem find_longest_palindrome_length (s : String) :
  (find_longest_palindrome s).length ≥ min 1 s.length :=
sorry

theorem find_longest_palindrome_maximal (s : String) (start len : Nat) :
  let substr := String.substring s start len
  substr.isPalindrome = true → (find_longest_palindrome s).length ≥ substr.length :=
sorry

theorem nonempty_input_nonempty_output (s : String) (h : s.length > 0) :
  (find_longest_palindrome s).length > 0 :=
sorry

theorem palindrome_input_returns_itself (s : String) (h : s.isPalindrome = true) :
  find_longest_palindrome s = s :=
sorry
-- </vc-theorems>