/-
Complete the  function `scramble(str1, str2)` that returns `true` if a portion of ```str1``` characters can be rearranged to match ```str2```, otherwise returns ```false```.

**Notes:**
* Only lower case letters will be used (a-z). No punctuation or digits will be included.
* Performance needs to be considered

## Examples

```python
scramble('rkqodlw', 'world') ==> True
scramble('cedewaraaossoqqyt', 'codewars') ==> True
scramble('katas', 'steak') ==> False
```
-/

def scramble (s1 s2 : String) : Bool :=
  sorry

-- Helper function to count char occurrences in string

-- <vc-helpers>
-- </vc-helpers>

def countChar (s : String) (c : Char) : Nat :=
  sorry

-- If scramble returns true, first string is at least as long as second

theorem scramble_length_property (s1 s2 : String) :
  s1.length > 0 → s2.length > 0 → scramble s1 s2 = true → s1.length ≥ s2.length :=
  sorry

-- A string can always be scrambled to form itself

theorem scramble_identical_strings (s : String) : 
  s.length > 0 → scramble s s = true :=
  sorry

-- If scramble is true, all chars in s2 appear at least as many times in s1

theorem scramble_subset_property (s1 s2 : String) (c : Char) :
  s1.length > 0 → s2.length > 0 → scramble s1 s2 = true →
  (countChar s2 c) ≤ (countChar s1 c) :=
  sorry

-- Any non-empty string can be scrambled to form empty string

theorem scramble_empty_second_string (s : String) :
  s.length > 0 → scramble s "" = true :=
  sorry

-- Empty string cannot form non-empty string

theorem scramble_empty_first_string (c : Char) :
  scramble "" (String.singleton c) = false :=
  sorry

-- Strings with disjoint character sets cannot be scrambled

theorem scramble_disjoint_alphabets (s1 s2 : String) :
  s1.length > 0 → s2.length > 0 →
  (∀ c, s1.contains c → ¬s2.contains c) →
  scramble s1 s2 = false :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval scramble "rkqodlw" "world"

/-
info: True
-/
-- #guard_msgs in
-- #eval scramble "cedewaraaossoqqyt" "codewars"

/-
info: False
-/
-- #guard_msgs in
-- #eval scramble "katas" "steak"

-- Apps difficulty: introductory
-- Assurance level: unguarded