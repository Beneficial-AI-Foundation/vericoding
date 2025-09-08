/-
Find the last element of the given argument(s).

## Examples

```python
last([1, 2, 3, 4]) ==>  4
last("xyz")        ==> "z"
last(1, 2, 3, 4)   ==>  4
```
In **javascript** and **CoffeeScript** a **list** will be an `array`, a `string` or the list of `arguments`.

(courtesy of [haskell.org](http://www.haskell.org/haskellwiki/99_questions/1_to_10))
-/

-- <vc-helpers>
-- </vc-helpers>

def last {α : Type} : α → α := sorry
def last_list {α : Type} : List α → α := sorry

theorem last_list_property {α : Type} (l : List α) (h : l ≠ []) :
  ∃ x, last_list l = x := sorry

theorem last_vararg_property {α : Type} (l : List α) (h : l ≠ []) :
  ∃ x, last l.head = x := sorry

theorem last_string_property (s : String) (h : s.length > 0) :
  ∃ c, last_list s.data = c := sorry

theorem last_tuple_property {α : Type} (a b c d : α) :
  last d = d := sorry

theorem last_single_property {α : Type} (x : α) :
  last x = x := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval last [1, 2, 3, 4, 5]

/-
info: 4
-/
-- #guard_msgs in
-- #eval last 1 2 3 4

/-
info: 'z'
-/
-- #guard_msgs in
-- #eval last "xyz"

-- Apps difficulty: introductory
-- Assurance level: unguarded