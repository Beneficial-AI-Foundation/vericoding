You will be given a string and you task is to check if it is possible to convert that string into a palindrome by removing a single character. If the string is already a palindrome, return `"OK"`. If it is not, and we can convert it to a palindrome by removing one character, then return `"remove one"`, otherwise return `"not possible"`. The order of the characters should not be changed.

For example:
```Haskell
solve("abba") = "OK". -- This is a palindrome
solve("abbaa") = "remove one". -- remove the 'a' at the extreme right. 
solve("abbaab") = "not possible". 
```

More examples in the test cases. 

Good luck!

If you like this Kata, please try [Single Character Palindromes II](https://www.codewars.com/kata/5a66ea69e6be38219f000110)

def solve (s : String) : String := sorry

def isPalindrome (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
