-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def palindrome (x : Int) : Bool ⊕ String := 
  sorry

def isDigitPalindrome (s : String) : Bool :=
  sorry

def reverseInt (n : Int) : Int := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem palindrome_output_type (x : Int) :
  x > 0 → Sum.casesOn (palindrome x) (fun _ => True) (fun _ => True) :=
sorry

theorem palindrome_correctness (x : Int) :
  x > 0 → match palindrome x with
  | .inl true => isDigitPalindrome (toString x) = true
  | .inl false => isDigitPalindrome (toString x) = false
  | .inr _ => False
  :=
sorry

theorem palindrome_negative_invalid (x : Int) :
  x ≤ 0 → palindrome x = .inr "Not valid" :=
sorry

theorem single_digit_palindrome (x : Int) :
  x > 0 → x < 10 → (palindrome x) = .inl true :=
sorry

theorem palindrome_concat_property (x : Int) :
  x > 0 →
  let xStr := toString x
  let palindromeNum := x * (10 ^ (String.length xStr)) + reverseInt x
  palindrome palindromeNum = .inl true :=
sorry
-- </vc-theorems>