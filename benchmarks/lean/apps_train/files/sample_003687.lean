If we alternate the vowels and consonants in the string `"have"`, we get the following list, arranged alphabetically:
`['ahev', 'aveh', 'ehav', 'evah', 'vahe', 'veha']`. These are the only possibilities in which vowels and consonants are alternated. The first element, `ahev`, is alphabetically lowest. 

Given a string:
* alternate the vowels and consonants and return the lexicographically lowest element in the list
* If any two or more vowels or consonants must follow each other, return `"failed"`
* if the number of vowels and consonants are equal, the first letter of the result must be a vowel.

Examples: 

```Haskell
solve("codewars") = "failed". However you alternate vowels and consonants, two consonants must follow each other
solve("oruder") = "edorur"
solve("orudere") = "ederoru". This is the only option that allows you to alternate vowels & consonants.
```

```if c:
In C, return an allocated string even if the response is "failed".
```

Vowels will be any of "aeiou". Input will be a lowercase string, no spaces. See test cases for more examples. 

Good luck!

If you like this Kata, please try: 

[Consonant value](https://www.codewars.com/kata/59c633e7dcc4053512000073)

[Alternate capitalization](https://www.codewars.com/kata/59cfc000aeb2844d16000075)

def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded