-- <vc-helpers>
-- </vc-helpers>

def findNearestPalindrome (n : Int) : String := sorry

def isPalindrome (n : String) : Bool := sorry

theorem finds_valid_palindrome (n : Int) 
  (h : 0 ≤ n ∧ n ≤ 10000) 
  (h2 : findNearestPalindrome n ≠ "Not valid") :
  isPalindrome (findNearestPalindrome n) := sorry

theorem negative_returns_not_valid (n : Int)
  (h : n < 0) : 
  findNearestPalindrome n = "Not valid" := sorry

theorem single_digit_returns_eleven (n : Int)
  (h : 0 ≤ n ∧ n ≤ 9) :
  findNearestPalindrome n = "11" := sorry

theorem palindrome_returns_self (n : Int)
  (h1 : 10 ≤ n ∧ n ≤ 10000)
  (h2 : isPalindrome (toString n)) :
  findNearestPalindrome n = toString n := sorry

/-
info: 11
-/
-- #guard_msgs in
-- #eval find_nearest_palindrome 8

/-
info: 282
-/
-- #guard_msgs in
-- #eval find_nearest_palindrome 281

/-
info: 1001
-/
-- #guard_msgs in
-- #eval find_nearest_palindrome 1029

/-
info: 1221
-/
-- #guard_msgs in
-- #eval find_nearest_palindrome 1221

/-
info: 'Not valid'
-/
-- #guard_msgs in
-- #eval find_nearest_palindrome "1221"

-- Apps difficulty: introductory
-- Assurance level: unguarded