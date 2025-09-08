/-
Your task is to ___Reverse and Combine Words___. It's not too difficult, but there are some things you have to consider...

### So what to do?

Input: String containing different "words" separated by spaces

```
1. More than one word? Reverse each word and combine first with second, third with fourth and so on...
   (odd number of words => last one stays alone, but has to be reversed too)
2. Start it again until there's only one word without spaces
3. Return your result...
```

### Some easy examples:
```
Input:  "abc def"
Output: "cbafed"

Input:  "abc def ghi 123"
Output: "defabc123ghi"

Input:  "abc def gh34 434ff 55_eri 123 343"
Output: "43hgff434cbafed343ire_55321"
```

I think it's clear?! First there are some static tests, later on random tests too...

### Hope you have fun! :-)
-/

def reverseAndCombineText (text : String) : String := sorry 

-- Result length should match total chars across merged words

-- <vc-helpers>
-- </vc-helpers>

def countChar (c : Char) (s : String) : Nat :=
  (s.toList.filter (· = c)).length

theorem output_length_matches_input_chars (text : String) : 
  String.length (reverseAndCombineText text) = 
  String.length (String.replace text " " "") := sorry

-- All input chars should appear in output in same quantities

theorem chars_preserved (text : String) (c : Char) : 
  countChar c (String.replace text " " "") = 
  countChar c (reverseAndCombineText text) := sorry

-- Number of words should roughly halve each iteration

theorem halves_words_per_iteration (text : String) :
  let wordCount := (text.split (· = ' ')).length
  let maxIterations := if wordCount ≤ 1 then 0 
                       else (wordCount - 1).log2 + 1
  ∀ result : String, result = reverseAndCombineText text →
  (result.split (· = ' ')).length ≤ 
    if wordCount ≤ 1 then 1 else wordCount / (2 ^ maxIterations) := sorry

/-
info: 'cbafed'
-/
-- #guard_msgs in
-- #eval reverse_and_combine_text "abc def"

/-
info: 'defabcjklghi'
-/
-- #guard_msgs in
-- #eval reverse_and_combine_text "abc def ghi jkl"

/-
info: 'trzwqfdstrteettr45hh4325543544hjhjh21lllll'
-/
-- #guard_msgs in
-- #eval reverse_and_combine_text "234hh54 53455 sdfqwzrt rtteetrt hjhjh lllll12  44"

-- Apps difficulty: introductory
-- Assurance level: unguarded