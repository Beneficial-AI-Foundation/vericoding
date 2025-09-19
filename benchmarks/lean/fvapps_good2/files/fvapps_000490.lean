-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_palindrome (s : String) : String :=
sorry

def isPalindrome (s : String) : Bool :=
sorry

def stringReverse (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortest_palindrome_contains_original (s : String) :
  (shortest_palindrome s).endsWith s :=
sorry

theorem shortest_palindrome_is_palindrome (s : String) :
  isPalindrome (shortest_palindrome s) = true :=
sorry

theorem shortest_palindrome_minimal_length (s : String) :
  (shortest_palindrome s).length ≤ 2 * s.length :=
sorry

theorem shortest_palindrome_empty_single_char (s : String) :
  s = "" ∨ s.length = 1 → shortest_palindrome s = s :=
sorry

theorem shortest_palindrome_starts_with_reversed_suffix (s : String) :
  s ≠ "" →
  let result := shortest_palindrome s
  let suffixLen := result.length - s.length
  suffixLen > 0 →
  (result.take suffixLen) = stringReverse (s.takeRight suffixLen) :=
sorry

theorem shortest_palindrome_single_char_string (s : String) (c : Char) :
  s.all (· = c) → shortest_palindrome s = s :=
sorry
-- </vc-theorems>