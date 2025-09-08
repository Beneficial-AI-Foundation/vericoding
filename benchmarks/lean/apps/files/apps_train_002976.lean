/-
In this kata you need to build a function to return either `true/True` or `false/False` if a string can be seen as the repetition of a simpler/shorter subpattern or not.

For example:

```cpp,java
hasSubpattern("a") == false; //no repeated pattern
hasSubpattern("aaaa") == true; //created repeating "a"
hasSubpattern("abcd") == false; //no repeated pattern
hasSubpattern("abababab") == true; //created repeating "ab"
hasSubpattern("ababababa") == false; //cannot be entirely reproduced repeating a pattern
```
```python
has_subpattern("a") == False #no repeated pattern
has_subpattern("aaaa") == True #created repeating "a"
has_subpattern("abcd") == False #no repeated pattern
has_subpattern("abababab") == True #created repeating "ab"
has_subpattern("ababababa") == False #cannot be entirely reproduced repeating a pattern
```
Strings will never be empty and can be composed of any character (just consider upper- and lowercase letters as different entities) and can be pretty long (keep an eye on performances!).

If you liked it, go for the [next kata](https://www.codewars.com/kata/string-subpattern-recognition-ii/) of the series!
-/

-- <vc-helpers>
-- </vc-helpers>

def has_subpattern (s : String) : Bool := sorry

theorem single_char_no_pattern (s : String) :
  s.length = 1 → ¬(has_subpattern s) := sorry

theorem doubled_string_has_pattern (s : String) : 
  s.length > 0 → has_subpattern (s ++ s) := sorry

theorem pattern_preserved_by_repetition (s : String) :
  s.length > 0 → has_subpattern s → 
  (has_subpattern (s ++ s ++ s) ∧ has_subpattern (s ++ s ++ s ++ s)) := sorry

theorem pattern_length_divides_string_length (s : String) :
  s.length > 0 → has_subpattern s → 
  ∃ i : Nat, i > 0 ∧ i ≤ s.length ∧ s.length % i = 0 := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval has_subpattern "a"

/-
info: True
-/
-- #guard_msgs in
-- #eval has_subpattern "aaaa"

/-
info: True
-/
-- #guard_msgs in
-- #eval has_subpattern "abababab"

-- Apps difficulty: introductory
-- Assurance level: unguarded