/-
Given a lowercase string that has alphabetic characters only and no spaces, return the highest value of consonant substrings. Consonants are any letters of the alphabet except `"aeiou"`. 

We shall assign the following values: `a = 1, b = 2, c = 3, .... z = 26`.

For example, for the word "zodiacs", let's cross out the vowels. We get: "z **~~o~~** d **~~ia~~** cs"

For C: do not mutate input.

More examples in test cases. Good luck!

If you like this Kata, please try:

[Word values](https://www.codewars.com/kata/598d91785d4ce3ec4f000018)

[Vowel-consonant lexicon](https://www.codewars.com/kata/59cf8bed1a68b75ffb000026)
-/

def solve (s : String) : Int := sorry

def isVowel (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def isConsonant (c : Char) : Bool := sorry

theorem solve_returns_nonnegative (s : String) : 
  solve s ≥ 0 := sorry

/-
info: 26
-/
-- #guard_msgs in
-- #eval solve "zodiac"

/-
info: 57
-/
-- #guard_msgs in
-- #eval solve "strength"

/-
info: 73
-/
-- #guard_msgs in
-- #eval solve "catchphrase"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible