/-
Your job is to figure out the index of which vowel is missing from a given string:

* `A` has an index of 0,
* `E` has an index of 1, 
* `I` has an index of 2, 
* `O` has an index of 3,
* `U` has an index of 4.

**Notes:** There is no need for string validation and every sentence given will contain all vowles but one. Also, you won't need to worry about capitals.

## Examples

```
"John Doe hs seven red pples under his bsket"          =>  0  ; missing: "a"
"Bb Smith sent us six neatly arranged range bicycles"  =>  3  ; missing: "o"
```
-/

def absent_vowel (s : String) : VowelIndex := 
  sorry

-- <vc-helpers>
-- </vc-helpers>

def getVowel (i : Nat) : Char :=
  match i with
  | 0 => 'a'
  | 1 => 'e'
  | 2 => 'i'
  | 3 => 'o'
  | _ => 'u'

theorem output_is_valid_index {s : String} (h : s.length > 0) :
  (absent_vowel s).val ≤ 4 :=
  sorry

theorem identified_vowel_actually_missing {s : String} (h : s.length > 0) :
  let result := (absent_vowel s).val
  ¬ s.contains (getVowel result) :=
  sorry

theorem only_one_vowel_missing {s : String} (h : s.length > 0) :
  let vowels := "aeiou"
  let text_vowels_count := (List.filter (fun c => vowels.contains c) s.data).length
  text_vowels_count = 4 →
  ¬ s.contains (getVowel (absent_vowel s).val) :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval absent_vowel "John Doe hs seven red pples under his bsket"

/-
info: 3
-/
-- #guard_msgs in
-- #eval absent_vowel "Bb Smith sent us six neatly arranged range bicycles"

-- Apps difficulty: introductory
-- Assurance level: guarded