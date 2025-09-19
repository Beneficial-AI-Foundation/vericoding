-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def palindrome (n : Int) : String :=
sorry

def isNumericPalindrome (n : Int) : Bool :=
sorry

def contains (haystack : String) (needle : String) : Bool :=
sorry

def stringToInt (s : String) : Option Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_input_negative (n : Int) :
  n < 0 → palindrome n = "Not valid"
  :=
sorry

theorem valid_input_contains_palindromes (n : Int) :
  n ≥ 0 → palindrome n ≠ "Not valid" →
  let result := palindrome n
  let numStr := toString n
  ∀ p ∈ result.split (· = ','),
    (∃ s : String, s = p ∧ contains numStr s ∧
      match stringToInt s with
      | some i => isNumericPalindrome i
      | none => false)
  :=
sorry

theorem valid_input_sorted_results (n : Int) :
  n ≥ 0 → palindrome n ≠ "Not valid" →
  let result := palindrome n
  let nums := result.split (· = ',')
  ∀ i j, i < j → j < nums.length →
    match stringToInt (nums.get! i), stringToInt (nums.get! j) with
    | some x, some y => x ≤ y
    | _, _ => true
  :=
sorry

theorem no_palindromes_when_none_exist (n : Int) (numStr : String := toString n) :
  n ≥ 0 →
  (∀ s : String, contains numStr s →
    match stringToInt s with
    | some i => ¬isNumericPalindrome i
    | none => true) →
  palindrome n = "No palindromes found"
  :=
sorry

theorem invalid_input_float (f : Float) :
  palindrome 0 = "Not valid"
  :=
sorry
-- </vc-theorems>