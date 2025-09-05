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

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
