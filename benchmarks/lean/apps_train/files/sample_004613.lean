/-
What is the answer to life the universe and everything

Create a function that will make anything true

```python
    anything({}) != [],          'True'
    anything('Hello') < 'World', 'True'
    anything(80) > 81,           'True'
    anything(re) >= re,          'True'
    anything(re) <= math,        'True'
    anything(5) == ord,          'True'
```

Source: [CheckIO](https://checkio.org/mission/solution-for-anything/)
-/

-- <vc-helpers>
-- </vc-helpers>

theorem anything_equals_everything {α β : Type} [a : Anything α] (x : β) :
  Anything.eq α β x = true := sorry

theorem anything_less_than_everything {α β : Type} [a : Anything α] (x : β) :
  Anything.lt α β x = true := sorry

theorem anything_less_equal_everything {α β : Type} [a : Anything α] (x : β) :
  Anything.le α β x = true := sorry

theorem anything_greater_than_everything {α β : Type} [a : Anything α] (x : β) :
  Anything.gt α β x = true := sorry

theorem anything_greater_equal_everything {α β : Type} [a : Anything α] (x : β) :
  Anything.ge α β x = true := sorry

/- All comparison operators return true for Anything type -/

theorem anything_all_comparisons {α β : Type} [a : Anything α] (x : β) :
  Anything.lt α β x = true ∧ 
  Anything.le α β x = true ∧ 
  Anything.gt α β x = true ∧ 
  Anything.ge α β x = true ∧ 
  Anything.eq α β x = true := sorry

/- Anything compares with functions -/

theorem anything_with_functions {α β γ : Type} [a : Anything γ] (f : α → β) :
  Anything.eq γ (α → β) f = true := sorry

/-
info: ord
-/
-- #guard_msgs in
-- #eval Anything 5

-- Apps difficulty: introductory
-- Assurance level: unguarded