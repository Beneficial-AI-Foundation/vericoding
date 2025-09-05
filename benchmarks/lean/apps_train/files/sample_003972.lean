Create a function `isAlt()` that accepts a string as an argument and validates whether the vowels (a, e, i, o, u) and consonants are in alternate order.

```python
is_alt("amazon")
// true
is_alt("apple")
// false
is_alt("banana")
// true
```

Arguments consist of only lowercase letters.

def VOWELS : List Char := ['a', 'e', 'i', 'o', 'u']

def isVowel (c : Char) : Bool := c ∈ VOWELS

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded