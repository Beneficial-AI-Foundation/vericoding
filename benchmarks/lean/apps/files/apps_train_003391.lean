-- <vc-helpers>
-- </vc-helpers>

def powerset {α : Type} (l : List α) : List (List α) :=
  sorry

theorem powerset_length {α : Type} (l : List α) : 
  (powerset l).length = 2 ^ l.length := by
  sorry

theorem powerset_contains_empty {α : Type} (l : List α) :
  [] ∈ powerset l := by
  sorry

theorem powerset_contains_full {α : Type} (l : List α) (h : l ≠ []) :
  l ∈ powerset l := by
  sorry

theorem powerset_elements_are_lists {α : Type} (l : List α) :
  ∀ x ∈ powerset l, x matches List.cons _ _ ∨ x = [] := by
  sorry

theorem powerset_subsets {α : Type} [BEq α] (l : List α) :
  ∀ subset ∈ powerset l, ∀ x ∈ subset, x ∈ l := by
  sorry

/-
info: [[], [2], [1], [1, 2]]
-/
-- #guard_msgs in
-- #eval powerset [1, 2]

/-
info: [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]]
-/
-- #guard_msgs in
-- #eval powerset [1, 2, 3]

/-
info: [[], [1]]
-/
-- #guard_msgs in
-- #eval powerset [1]

-- Apps difficulty: introductory
-- Assurance level: guarded