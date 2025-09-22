-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def valid_palindrome (s : String) : Bool :=
sorry

def reverse (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def isPalindrome (s : String) : Bool := s == reverse s

theorem palindrome_basic (s : String) :
  isPalindrome s → valid_palindrome s :=
sorry

theorem single_char_palindrome (s : String) :
  s.length ≤ 1 → valid_palindrome s :=
sorry

theorem palindrome_remove_char (s : String) :
  s.length > 1 → isPalindrome s →
  valid_palindrome (s.take (s.length - 1)) :=
sorry

theorem nearly_palindrome (s : String) (x : Char) :
  s.length ≥ 3 →
  let palindrome := s ++ reverse s
  let middle := palindrome.length / 2
  let nearly_pal := palindrome.take middle ++ String.mk [x] ++ palindrome.drop middle
  valid_palindrome nearly_pal :=
sorry

theorem non_palindrome (s : String) :
  s.length ≥ 2 →
  ¬(isPalindrome s) →
  (let count := (List.zip s.data (reverse s).data).filter (fun p => p.1 ≠ p.2) |>.length
   count > 2) →
  ¬(valid_palindrome s) :=
sorry
-- </vc-theorems>