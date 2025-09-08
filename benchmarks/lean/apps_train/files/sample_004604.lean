/-
Write a function that takes a piece of text in the form of a string and returns the letter frequency count for the text. This count excludes numbers, spaces and all punctuation marks. Upper and lower case versions of a character are equivalent and the result should all be in lowercase.

The function should return a list of tuples (in Python and Haskell) or arrays (in other languages) sorted by the most frequent letters first. The Rust implementation should return an ordered BTreeMap.
Letters with the same frequency are ordered alphabetically.
For example:

```python
  letter_frequency('aaAabb dddDD hhcc')
```  
```C++
  letter_frequency("aaAabb dddDD hhcc")
```

will return

```python
  [('d',5), ('a',4), ('b',2), ('c',2), ('h',2)]
```  
```C++
  std::vector>{{'d',5}, {'a',4}, {'b',2}, {'c',2}, {'h',2}}
```

Letter frequency analysis is often used to analyse simple substitution cipher texts like those created by the Caesar cipher.
-/

-- <vc-helpers>
-- </vc-helpers>

def isAlpha (c : Char) : Bool := sorry

def letterFrequency (s : String) : List (Char × Nat) := sorry

theorem letterFrequency_output_structure 
  (s : String) :
  let result := letterFrequency s
  ∀ pair, pair ∈ result → 
    isAlpha pair.fst ∧ 
    pair.snd > 0 := sorry

theorem letterFrequency_ordering 
  (s : String) :
  let result := letterFrequency s  
  result ≠ [] →
  ∀ (i : Fin result.length) (j : Fin result.length),
    i.val < j.val →
    ((result.get i).snd > (result.get j).snd ∨ 
    ((result.get i).snd = (result.get j).snd ∧ 
     (result.get i).fst < (result.get j).fst)) := sorry

theorem letterFrequency_total_count
  (s : String) :
  let result := letterFrequency s
  List.foldl (λ acc pair => acc + pair.snd) 0 result = 
  List.length (s.data.filter isAlpha) := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval letter_frequency "aaAabb dddDD hhcc"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval letter_frequency "Hello! 123 World."

/-
info: expected3
-/
-- #guard_msgs in
-- #eval letter_frequency ""

-- Apps difficulty: introductory
-- Assurance level: unguarded