Given a string as input, move all of its vowels to the end of the string, in the same order as they were before.

Vowels are (in this kata): `a, e, i, o, u`

Note: all provided input strings are lowercase.

## Examples
```python
"day"    ==>  "dya"
"apple"  ==>  "pplae"
```

def move_vowels (s : String) : String := sorry

def is_vowel (c : Char) : Bool :=
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u'

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded