-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_troops_to_ruin (s: String) : Nat :=
sorry

def isPalindrome (s: String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_troops_bounds (s: String) :
  let result := find_min_troops_to_ruin s
  0 ≤ result ∧ result ≤ 2 :=
sorry

theorem empty_string_troops (s: String) :
  s = "" → find_min_troops_to_ruin s = 0 :=
sorry

theorem palindrome_troops (s: String) :
  s ≠ "" ∧ isPalindrome s → find_min_troops_to_ruin s = 1 :=
sorry

theorem non_palindrome_troops (s: String) :
  s ≠ "" ∧ ¬isPalindrome s → find_min_troops_to_ruin s = 2 :=
sorry
-- </vc-theorems>