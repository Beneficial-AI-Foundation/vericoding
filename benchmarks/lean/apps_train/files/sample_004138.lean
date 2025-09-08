/-
An isogram is a word that has no repeating letters, consecutive or non-consecutive. Implement a function that determines whether a string that contains only letters is an isogram. Assume the empty string is an isogram. Ignore letter case.

```python
is_isogram("Dermatoglyphics" ) == true
is_isogram("aba" ) == false
is_isogram("moOse" ) == false # -- ignore letter case
```
```C
is_isogram("Dermatoglyphics" ) == true;
is_isogram("aba" ) == false;
is_isogram("moOse" ) == false; // -- ignore letter case
```
-/

-- <vc-helpers>
-- </vc-helpers>

def is_isogram (s : String) : Bool := sorry

theorem empty_and_single_chars_are_isograms (s : String) :
  s.length ≤ 1 → is_isogram s := sorry

theorem repeated_chars_not_isogram (s : String) :
  s.length > 0 → ¬(is_isogram (s ++ String.mk [s.get 0])) := sorry

theorem all_unique_chars_is_isogram (s : String) :
  let unique_chars := String.mk (List.eraseDups s.data)
  is_isogram unique_chars := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_isogram "Dermatoglyphics"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_isogram "moOse"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_isogram ""

-- Apps difficulty: introductory
-- Assurance level: unguarded