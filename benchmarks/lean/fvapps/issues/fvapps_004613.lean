-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>