def find_closest_palindrome (s : String) : String := sorry

def isPalindrome (s : String) : Bool := sorry

def allCharsNumeric (s : String) : Bool := sorry

def toNat (s : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def toString! (n : Nat) : String := sorry

-- Basic type constraints

theorem find_closest_palindrome_outputs_nonempty {n : String} 
  (h : isPalindrome n = false) 
  : String.length (find_closest_palindrome n) > 0 := sorry

-- Result should be numeric

theorem find_closest_palindrome_is_numeric {n : String} 
  (h : isPalindrome n = false)
  : allCharsNumeric (find_closest_palindrome n) = true := sorry

-- Result differs from input  

theorem find_closest_palindrome_different {n : String} 
  (h : isPalindrome n = false)
  : find_closest_palindrome n ≠ n := sorry

-- Result length within ±1 of input length

theorem find_closest_palindrome_length {n : String} 
  (h : isPalindrome n = false)
  : (String.length (find_closest_palindrome n)).sub (String.length n) ≤ 1 ∧ 
    (String.length n).sub (String.length (find_closest_palindrome n)) ≤ 1 := sorry

-- Result is palindromic

theorem find_closest_palindrome_is_palindrome {n : String} 
  (h : isPalindrome n = false)
  : isPalindrome (find_closest_palindrome n) = true := sorry

-- Result doesn't start with '0' 

theorem find_closest_palindrome_no_leading_zero {n : String} 
  (h : isPalindrome n = false)
  : String.get! (find_closest_palindrome n) 0 ≠ '0' := sorry

-- Result is closest palindrome (minimality)

theorem find_closest_palindrome_is_minimal {n : String} 
  (h : isPalindrome n = false)
  (h2 : String.length n ≥ 1)
  : let result := find_closest_palindrome n
    let diff := (toNat result).sub (toNat n)
    ∀ k : Nat, 
      k ≠ toNat n → 
      isPalindrome (toString! k) = true →
      (k.sub (toNat n)).min ((toNat n).sub k) ≥ diff := sorry

/-
info: '121'
-/
-- #guard_msgs in
-- #eval find_closest_palindrome "123"

/-
info: '999'
-/
-- #guard_msgs in
-- #eval find_closest_palindrome "1000"

/-
info: '1001'
-/
-- #guard_msgs in
-- #eval find_closest_palindrome "999"

-- Apps difficulty: interview
-- Assurance level: unguarded