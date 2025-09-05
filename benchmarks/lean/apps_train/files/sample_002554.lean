Complete the method so that it formats the words into a single comma separated value. The last word should be separated by the word 'and' instead of a comma. The method takes in an array of strings and returns a single formatted string. Empty string values should be ignored. Empty arrays or null/nil values being passed into the method should result in an empty string being returned. 

```Python
format_words(['ninja', 'samurai', 'ronin']) # should return "ninja, samurai and ronin"
format_words(['ninja', '', 'ronin']) # should return "ninja and ronin"
format_words([]) # should return ""
```
```Haskell
formatWords ["ninja", "samurai", "ronin"] -- should return "ninja, samurai and ronin"
formatWords ["ninja", "", "ronin"] -- should return "ninja and ronin"
formatWords [] -- should return ""
```

def format_words (words : List String) : String := sorry

def String.countSubstr (s1 s2 : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
