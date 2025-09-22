-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_closest_palindrome (s : String) : String :=
sorry

def isPalindrome (s : String) : Bool :=
sorry

def allCharsNumeric (s : String) : Bool :=
sorry

def toNat (s : String) : Nat :=
sorry

def toString! (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_closest_palindrome_outputs_nonempty {n : String}
  (h : isPalindrome n = false)
  : String.length (find_closest_palindrome n) > 0 :=
sorry

theorem find_closest_palindrome_is_numeric {n : String}
  (h : isPalindrome n = false)
  : allCharsNumeric (find_closest_palindrome n) = true :=
sorry

theorem find_closest_palindrome_different {n : String}
  (h : isPalindrome n = false)
  : find_closest_palindrome n ≠ n :=
sorry

theorem find_closest_palindrome_length {n : String}
  (h : isPalindrome n = false)
  : (String.length (find_closest_palindrome n)).sub (String.length n) ≤ 1 ∧
    (String.length n).sub (String.length (find_closest_palindrome n)) ≤ 1 :=
sorry

theorem find_closest_palindrome_is_palindrome {n : String}
  (h : isPalindrome n = false)
  : isPalindrome (find_closest_palindrome n) = true :=
sorry

theorem find_closest_palindrome_no_leading_zero {n : String}
  (h : isPalindrome n = false)
  : String.get! (find_closest_palindrome n) 0 ≠ '0' :=
sorry

theorem find_closest_palindrome_is_minimal {n : String}
  (h : isPalindrome n = false)
  (h2 : String.length n ≥ 1)
  : let result := find_closest_palindrome n
    let diff := (toNat result).sub (toNat n)
    ∀ k : Nat,
      k ≠ toNat n →
      isPalindrome (toString! k) = true →
      (k.sub (toNat n)).min ((toNat n).sub k) ≥ diff :=
sorry
-- </vc-theorems>