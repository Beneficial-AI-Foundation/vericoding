/-
Write a function that checks the braces status in a string, and return `True` if all braces are properly closed, or `False` otherwise. Available types of brackets: `()`, `[]`, `{}`.

**Please note, you need to write this function without using regex!**

## Examples
```python
'([[some](){text}here]...)'  =>  True
'{([])}'                     =>  True
'()[]{}()'                   =>  True
'(...[]...{(..())}[abc]())'  =>  True
'1239(df){'                  =>  False
'[()])'                      =>  False
')12[x]34('                  =>  False
```
Don't forget to rate this kata! Thanks :)
-/

-- <vc-helpers>
-- </vc-helpers>

def braces_status (s : String) : Bool := sorry

def count (c : Char) (s : String) : Nat := sorry

theorem braces_status_balanced (s : String) :
  braces_status s = true →
  count '(' s = count ')' s ∧ 
  count '[' s = count ']' s ∧
  count '{' s = count '}' s := sorry

theorem only_opening_braces (s : String) :
  (∀ c, c ∈ s.data → c ∈ ['(', '[', '{']) →
  (s ≠ "" → braces_status s = false) := sorry

theorem only_closing_braces (s : String) :
  (∀ c, c ∈ s.data → c ∈ [')', ']', '}']) →
  (s ≠ "" → braces_status s = false) := sorry

theorem empty_string_balanced :
  braces_status "" = true := sorry

theorem non_bracket_chars (s : String) :
  (∀ c, c ∈ s.data → c ∉ ['(', ')', '[', ']', '{', '}']) →
  braces_status s = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval braces_status "[()]"

/-
info: False
-/
-- #guard_msgs in
-- #eval braces_status "([)]"

/-
info: True
-/
-- #guard_msgs in
-- #eval braces_status "()[]{}()"

-- Apps difficulty: introductory
-- Assurance level: unguarded