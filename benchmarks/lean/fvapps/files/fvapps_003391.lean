-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def powerset {α : Type} (l : List α) : List (List α) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>