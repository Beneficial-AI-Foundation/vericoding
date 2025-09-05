Create a function that takes a string as a parameter and does the following, in this order:

1. replaces every letter with the letter following it in the alphabet (see note below)
2. makes any vowels capital
3. makes any consonants lower case

**Note:** the alphabet should wrap around, so `Z` becomes `A`

So, for example the string `"Cat30"` would return `"dbU30"` (`Cat30 --> Dbu30 --> dbU30`)

def String.isAlpha : Char → Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
