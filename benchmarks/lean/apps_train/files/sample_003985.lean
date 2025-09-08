/-
A palindrome is a word, phrase, number, or other sequence of characters which reads the same backward as forward. Examples of numerical palindromes are: 

2332
110011
54322345

For a given number ```num```, return its closest numerical palindrome which can either be smaller or larger than ```num```. If there are 2 possible values, the larger value should be returned. If ```num``` is a numerical palindrome itself, return it. 

For this kata, single digit numbers will NOT be considered numerical palindromes. 

Also, you know the drill - be sure to return "Not valid" if the input is not an integer or is less than 0.

```
palindrome(8) => 11
palindrome(281) => 282 
palindrome(1029) => 1001
palindrome(1221) => 1221
palindrome("1221") => "Not valid"

```

```Haskell
In Haskell the function should return a Maybe Int with Nothing for cases where the argument is less than zero.
```
Other Kata in this Series:
Numerical Palindrome #1
Numerical Palindrome #1.5
Numerical Palindrome #2
Numerical Palindrome #3
Numerical Palindrome #3.5
Numerical Palindrome #4
Numerical Palindrome #5
-/

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