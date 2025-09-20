-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : String :=
sorry

def isPalindrome (s : String) : Bool :=
sorry

def canBePalindromeWithOneRemoval (s : String) : Bool :=
sorry

def reverse (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_valid (s : String) :
  solve s = "OK" ∨ solve s = "remove one" ∨ solve s = "not possible" :=
sorry

theorem ok_means_palindrome (s : String) :
  solve s = "OK" → isPalindrome s :=
sorry

theorem remove_one_means_possible_palindrome (s : String) :
  solve s = "remove one" → canBePalindromeWithOneRemoval s :=
sorry

theorem not_possible_means_neither (s : String) :
  solve s = "not possible" → ¬isPalindrome s ∧ ¬canBePalindromeWithOneRemoval s :=
sorry

theorem solve_symmetric (s : String) :
  solve s = solve (reverse s) :=
sorry

theorem single_char_ok (s : String) :
  s.length = 1 → solve s = "OK" :=
sorry

theorem two_chars_property (s : String) (h : s.length = 2) :
  (s.front = s.back → solve s = "OK") ∧
  (s.front ≠ s.back → solve s = "remove one") :=
sorry
-- </vc-theorems>