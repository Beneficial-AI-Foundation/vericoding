/-
A palindrome is a word, phrase, number, or other sequence of characters which reads the same backward as forward. Examples of numerical palindromes are: 

2332
110011
54322345

For a given number ```num```, write a function which returns the number of numerical palindromes within each number. For this kata, single digit numbers will NOT be considered numerical palindromes. 

Return "Not valid" if the input is not an integer or is less than 0.

```
palindrome(5) => 0
palindrome(1221) => 2 
palindrome(141221001) => 5  
palindrome(1294) => 0
palindrome("1221") => "Not valid"

```

```Haskell
In Haskell, return a Maybe Int with Nothing for negative numbers.
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

def palindrome (n : Int) : Int :=
  sorry

theorem palindrome_outputs_int {x : Int} (h : x ≥ 0) :
  ∃ y : Int, palindrome x = y :=
  sorry

theorem palindrome_negative_rejects (x : Int) (h : x < 0) :
  palindrome x = -1 := -- assuming -1 represents 'Not valid'
  sorry

theorem palindrome_single_digit {x : Int} (h1 : x ≥ 0) (h2 : x ≤ 9) :
  palindrome x = 0 :=
  sorry

theorem palindrome_output_non_negative {x : Int} (h : x ≥ 0) :
  palindrome x ≥ 0 :=
  sorry

theorem palindrome_detects_basic {x : Int} (h : x = 1221) :
  palindrome x > 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval palindrome 2

/-
info: 5
-/
-- #guard_msgs in
-- #eval palindrome 141221001

/-
info: 'Not valid'
-/
-- #guard_msgs in
-- #eval palindrome "1551"

-- Apps difficulty: introductory
-- Assurance level: unguarded