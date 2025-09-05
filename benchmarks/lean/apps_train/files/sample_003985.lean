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

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
