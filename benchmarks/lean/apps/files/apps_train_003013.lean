/-
Create a function `longer` that accepts a string and sorts the words in it based on their respective lengths in an ascending order. If there are two words of the same lengths, sort them alphabetically. Look at the examples below for more details.

```python
longer("Another Green World") => Green World Another
longer("Darkness on the edge of Town") => of on the Town edge Darkness
longer("Have you ever Seen the Rain") => the you Have Rain Seen ever
```

Assume that only only Alphabets will be entered as the input.
Uppercase characters have priority over lowercase characters. That is,
```python
longer("hello Hello") => Hello hello
```

Don't forget to rate this kata and leave your feedback!! 
Thanks
-/

-- <vc-helpers>
-- </vc-helpers>

def longer (s : String) : String := sorry

instance : LE (Nat × String) where
  le := fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

theorem longer_sorted_property {s : String} {result : String} (h : result = longer s) 
  (h_nonempty : s ≠ "") :
  let words := result.split (· = ' ')
  ∀ i, i + 1 < words.length → 
    (words[i]!.length, words[i]!) ≤ (words[i+1]!.length, words[i+1]!)
  := sorry

theorem longer_preserves_unique_words {s : String} {result : String} 
  (h : result = longer s) :
  let input_words := s.split (· = ' ')
  let output_words := result.split (· = ' ')
  ∀ w, w ∈ input_words ↔ w ∈ output_words
  := sorry

/-
info: 'Green World Another'
-/
-- #guard_msgs in
-- #eval longer "Another Green World"

/-
info: 'of on the Town edge Darkness'
-/
-- #guard_msgs in
-- #eval longer "Darkness on the edge of Town"

/-
info: 'Hello hello'
-/
-- #guard_msgs in
-- #eval longer "hello Hello"

-- Apps difficulty: introductory
-- Assurance level: unguarded