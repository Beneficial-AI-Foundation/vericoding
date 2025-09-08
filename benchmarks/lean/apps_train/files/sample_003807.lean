/-
A spoonerism is a spoken phrase in which the first letters of two of the words are swapped around, often with amusing results.

In its most basic form a spoonerism is a two word phrase in which only the first letters of each word are swapped:

```"not picking" --> "pot nicking"```

Your task is to create a function that takes a string of two words, separated by a space: ```words``` and returns a spoonerism of those words in a string, as in the above example.

NOTE: All input strings will contain only two words.  Spoonerisms can be more complex.  For example, three-word phrases in which the first letters of the first and last words are swapped: ```"pack of lies" --> "lack of pies"``` or more than one letter from a word is swapped: ```"flat battery --> "bat flattery"```
You are NOT expected to account for these, or any other nuances involved in spoonerisms.

Once you have completed this kata, a slightly more challenging take on the idea can be found here: http://www.codewars.com/kata/56dbed3a13c2f61ae3000bcd
-/

-- <vc-helpers>
-- </vc-helpers>

def spoonerize (s : String) : String := sorry

theorem spoonerize_preserves_string_type {s : String} :
  s.contains ' ' ∧ (s.split (· == ' ')).length = 2 →
  spoonerize s ≠ "" := sorry

theorem spoonerize_single_space {s : String} :
  s.contains ' ' ∧ (s.split (· == ' ')).length = 2 →
  ((spoonerize s).data.filter (· == ' ')).length = 1 := sorry

theorem spoonerize_preserves_length {s : String} :
  s.contains ' ' ∧ (s.split (· == ' ')).length = 2 →
  (spoonerize s).length = s.length := sorry

theorem spoonerize_preserves_chars {s : String} :
  s.contains ' ' ∧ (s.split (· == ' ')).length = 2 →
  ∀ c, (s.data.filter (· == c)).length = ((spoonerize s).data.filter (· == c)).length := sorry

theorem spoonerize_swaps_first_letters {s : String} (w1 w2 : String)
  (h : s = w1 ++ String.mk [' '] ++ w2) (hw : w1 ≠ "" ∧ w2 ≠ "") :
  let r := spoonerize s
  let r1 := (r.split (· == ' ')).get! 0
  let r2 := (r.split (· == ' ')).get! 1
  r1.get! 0 = w2.get! 0 ∧ r2.get! 0 = w1.get! 0 := sorry

theorem spoonerize_preserves_rest {s : String} (w1 w2 : String)
  (h : s = w1 ++ String.mk [' '] ++ w2) (hw : w1 ≠ "" ∧ w2 ≠ "") :
  let r := spoonerize s
  let r1 := (r.split (· == ' ')).get! 0
  let r2 := (r.split (· == ' ')).get! 1
  List.drop 1 r1.data = List.drop 1 w1.data ∧ 
  List.drop 1 r2.data = List.drop 1 w2.data := sorry

theorem spoonerize_invalid_empty (s : String) :
  s = "" → spoonerize s = "" := sorry

theorem spoonerize_invalid_one_word (s : String) :
  (¬s.contains ' ') → spoonerize s = "" := sorry

theorem spoonerize_invalid_too_many (s : String) :
  (s.split (· == ' ')).length > 2 → spoonerize s = "" := sorry

/-
info: 'pot nicking'
-/
-- #guard_msgs in
-- #eval spoonerize "not picking"

/-
info: 'bedding wells'
-/
-- #guard_msgs in
-- #eval spoonerize "wedding bells"

/-
info: 'belly jeans'
-/
-- #guard_msgs in
-- #eval spoonerize "jelly beans"

-- Apps difficulty: introductory
-- Assurance level: unguarded