/-
Move the first letter of each word to the end of it, then add "ay" to the end of the word. Leave punctuation marks untouched.

## Examples

```python
pig_it('Pig latin is cool') # igPay atinlay siay oolcay
pig_it('Hello world !')     # elloHay orldway !
```
```C++
pig_it("Pig latin is cool");   // igPay atinlay siay oolcay
pig_it("Hello world !");       // elloHay orldway
```
```Java
PigLatin.pigIt('Pig latin is cool'); // igPay atinlay siay oolcay
PigLatin.pigIt('Hello world !');     // elloHay orldway !
```
-/

-- <vc-helpers>
-- </vc-helpers>

def pigLatin (s : String) : String := sorry 

theorem pigLatin_word_transform {word : String} 
  (h : ∀ c ∈ word.data, c.isAlpha) : 
  word.length > 0 → 
  pigLatin word = (word.drop 1) ++ (word.take 1) ++ "ay" := sorry

theorem pigLatin_word_count {text : String} :
  text.trim.length > 0 →
  ((pigLatin text).splitOn " ").length = (text.splitOn " ").length := sorry

theorem pigLatin_preserves_word_count {text : String} :
  text.length > 0 →
  text.trim.length > 0 →
  ((pigLatin text).splitOn " ").length = (text.splitOn " ").length := sorry

theorem pigLatin_word_list_transform {words : List String}
  (h : ∀ w ∈ words, ∀ c ∈ w.data, c.isAlpha) :
  words.length > 0 →
  (String.join words).splitOn " " = 
    words.map (λ w => (w.drop 1) ++ (w.take 1) ++ "ay") := sorry

/-
info: 'igPay atinlay siay oolcay'
-/
-- #guard_msgs in
-- #eval pig_it "Pig latin is cool"

/-
info: 'hisTay siay ymay tringsay'
-/
-- #guard_msgs in
-- #eval pig_it "This is my string"

/-
info: 'elloHay orldway !'
-/
-- #guard_msgs in
-- #eval pig_it "Hello world !"

-- Apps difficulty: introductory
-- Assurance level: unguarded