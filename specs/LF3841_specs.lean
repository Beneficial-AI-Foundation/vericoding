-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pig_latin (word : String) : String := sorry

theorem pig_latin_long_words (word : String)
  (h1 : word.length ≥ 4)
  : let result := pig_latin word
    (result.length = word.length + 2) ∧
    (result.endsWith "ay") ∧ 
    (result.dropRight 2 = word.drop 1 ++ word.take 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pig_latin_short_words (word : String)
  (h1 : word.length ≤ 3)
  : pig_latin word = word := sorry

theorem pig_latin_empty 
  : pig_latin "" = "" := sorry
-- </vc-theorems>