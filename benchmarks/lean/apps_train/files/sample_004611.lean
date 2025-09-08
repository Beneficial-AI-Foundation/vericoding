/-
My third kata, write a function `check_generator` that examines the status of a Python generator expression `gen` and returns `'Created'`, `'Started'` or `'Finished'`. For example:

`gen = (i for i in range(1))` >>> returns `'Created'` (the generator has been initiated)

`gen = (i for i in range(1)); next(gen, None)` >>> returns `'Started'` (the generator has yielded a value)

`gen = (i for i in range(1)); next(gen, None); next(gen, None)` >>> returns `'Finished'` (the generator has been exhuasted)

For an introduction to Python generators, read: https://wiki.python.org/moin/Generators.

Please do vote and rank the kata, and provide any feedback.

Hint: you can solve this if you know the right module to use.
-/

-- <vc-helpers>
-- </vc-helpers>

def check_generator {α : Type} (g : List α) : GeneratorState :=
  sorry

theorem new_generator {α : Type} (xs : List α) :
  check_generator xs = GeneratorState.Created := by
  sorry

theorem started_generator {α : Type} (xs : List α) (h : xs ≠ []) :
  check_generator (xs.tail) = GeneratorState.Started := by
  sorry

theorem finished_generator {α : Type} (xs : List α) :
  check_generator ([] : List α) = GeneratorState.Finished := by
  sorry

theorem generator_sequence {α : Type} (xs : List α) :
  (check_generator xs = GeneratorState.Created) ∧
  (xs ≠ [] → check_generator (xs.tail) = GeneratorState.Started) ∧
  (check_generator ([] : List α) = GeneratorState.Finished) := by
  sorry

theorem range_generator (n : Nat) :
  (check_generator (List.range n) = GeneratorState.Created) ∧
  (n > 0 → check_generator (List.range n).tail = GeneratorState.Started) ∧
  (check_generator ([] : List Nat) = GeneratorState.Finished) := by
  sorry

/-
info: 'Created'
-/
-- #guard_msgs in
-- #eval check_generator (i for i in range(2))

/-
info: 'Started'
-/
-- #guard_msgs in
-- #eval check_generator (i for i in range(2))

/-
info: 'Finished'
-/
-- #guard_msgs in
-- #eval check_generator (i for i in range(2))

-- Apps difficulty: introductory
-- Assurance level: unguarded