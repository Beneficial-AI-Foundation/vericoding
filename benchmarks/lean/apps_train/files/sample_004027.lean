/-
# Base64 Numeric Translator

Our standard numbering system is (Base 10). That includes 0 through 9. Binary is (Base 2), only 1’s and 0’s.  And Hexadecimal is (Base 16) (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F). A hexadecimal “F” has a (Base 10) value of 15. (Base 64) has 64 individual characters which translate in value in (Base 10) from between 0 to 63.

####Write a method that will convert a string from (Base 64) to it's (Base 10) integer value.

The (Base 64) characters from least to greatest will be
```
ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/
```
Where 'A' is equal to 0 and '/' is equal to 63.

Just as in standard (Base 10) when you get to the highest individual integer 9 the next number adds an additional place and starts at the beginning 10; so also (Base 64) when you get to the 63rd digit '/' and the next number adds an additional place and starts at the beginning "BA".

Example:
```
base64_to_base10("/") # => 63
base64_to_base10("BA") # => 64
base64_to_base10("BB") # => 65
base64_to_base10("BC") # => 66
```

Write a method `base64_to_base10` that will take a string (Base 64) number and output it's (Base 10) value as an integer.
-/

-- <vc-helpers>
-- </vc-helpers>

def DIGITS : List Char := sorry

def base64_to_base10 (s : String) : Nat := sorry

theorem base64_to_base10_nonnegative (s: String) 
  (h: s.length > 0)
  (h2: ∀ c ∈ s.data, c ∈ DIGITS) :
  base64_to_base10 s ≥ 0 := sorry

theorem base64_to_base10_longer_is_larger (s: String)
  (h: s.length > 1)
  (h2: ∀ c ∈ s.data, c ∈ DIGITS) :
  base64_to_base10 s > base64_to_base10 (String.dropRight s 1) := sorry

theorem base64_to_base10_matches_manual (s: String)
  (h: s.length > 0)
  (h2: ∀ c ∈ s.data, c ∈ DIGITS) :
  base64_to_base10 s = 
    (List.enum s.data.reverse).foldl
      (fun acc (i, c) => acc + (DIGITS.findIdx? (· = c)).get! * (64 ^ i)) 0 := sorry

theorem base64_to_base10_type (s: String)
  (h: s.length > 0)
  (h2: ∀ c ∈ s.data, c ∈ DIGITS) :
  base64_to_base10 s ≥ 0 := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded