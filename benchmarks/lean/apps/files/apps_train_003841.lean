/-
Task:
Make a function that converts a word to pig latin. The rules of pig latin are:

```
If the word has more than 3 letters:
  1. Take the first letter of a word and move it to the end
  2. Add -ay to the word
Otherwise leave the word alone.
```

Example: `hello` = `ellohay`
-/

-- <vc-helpers>
-- </vc-helpers>

def pig_latin (word : String) : String := sorry

theorem pig_latin_long_words (word : String)
  (h1 : word.length ≥ 4)
  : let result := pig_latin word
    (result.length = word.length + 2) ∧
    (result.endsWith "ay") ∧ 
    (result.dropRight 2 = word.drop 1 ++ word.take 1) := sorry

theorem pig_latin_short_words (word : String)
  (h1 : word.length ≤ 3)
  : pig_latin word = word := sorry

theorem pig_latin_empty 
  : pig_latin "" = "" := sorry

/-
info: 'ellohay'
-/
-- #guard_msgs in
-- #eval pig_latin "hello"

/-
info: 'hi'
-/
-- #guard_msgs in
-- #eval pig_latin "hi"

/-
info: 'orldway'
-/
-- #guard_msgs in
-- #eval pig_latin "world"

-- Apps difficulty: introductory
-- Assurance level: unguarded