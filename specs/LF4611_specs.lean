-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_generator {α : Type} (g : List α) : GeneratorState :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>