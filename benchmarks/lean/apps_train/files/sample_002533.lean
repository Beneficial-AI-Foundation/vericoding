In this Kata, you will check if it is possible to convert a string to a palindrome by changing one character. 

For instance:
```Haskell
solve ("abbx") = True, because we can convert 'x' to 'a' and get a palindrome. 
solve ("abba") = False, because we cannot get a palindrome by changing any character. 
solve ("abcba") = True. We can change the middle character. 
solve ("aa") = False 
solve ("ab") = True
```

Good luck!

Please also try [Single Character Palindromes](https://www.codewars.com/kata/5a2c22271f7f709eaa0005d3)

def solve (s : String) : Bool := sorry

def stringReverse (s : String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded