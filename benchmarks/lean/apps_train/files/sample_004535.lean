We will use the Flesch–Kincaid Grade Level to evaluate the readability of a piece of text. This grade level is an approximation for what schoolchildren are able to understand a piece of text. For example, a piece of text with a grade level of 7 can be read by seventh-graders and beyond.

The way to calculate the grade level is as follows:

    (0.39 * average number of words per sentence) + (11.8 * average number of syllables per word) - 15.59

Write a function that will calculate the Flesch–Kincaid grade level for any given string. Return the grade level rounded to two decimal points.

Ignore hyphens, dashes, apostrophes, parentheses, ellipses and abbreviations.

Remember that the text can contain more than one sentence: code accordingly!

**HINT**: Count the number of vowels as an approximation for the number of syllables, but count groups of vowels as one (e.g. `deal` is one syllable). **Do not** count `y` as a vowel!

## Example

```python
"The turtle is leaving." ==> 3.67
```

The average number of words per sentence is `4` and the average number of syllables per word is `1.5`. The score is then `(0.39 * 4) +  (11.8 * 1.5) - 15.59` = `3.67`

def count (s : String) (pattern : String) : Nat :=
  sorry

def SENTENCE : String :=
  sorry

def SYLLABLE : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded