-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort {α : Type} [Ord α] (xs : List α) : List α := sorry

theorem sort_length {α : Type} [Ord α] (xs : List α) :
  (sort xs).length = xs.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_ordered {α : Type} [Ord α] [LE α] (xs : List α) :
  ∀ i j, i < j → j < (sort xs).length → 
  (sort xs).get ⟨i, by sorry⟩ ≤ (sort xs).get ⟨j, by sorry⟩ := sorry

theorem sort_perm_elem {α : Type} [Ord α] [BEq α] (xs : List α) :
  ∀ x, List.elem x (sort xs) = List.elem x xs := sorry

theorem sort_first {α : Type} [Ord α] [LE α] (xs : List α) (h₁ : xs ≠ []) :
  ∀ x ∈ xs, (sort xs).get ⟨0, by sorry⟩ ≤ x := sorry

theorem sort_last {α : Type} [Ord α] [LE α] (xs : List α) (h₁ : xs ≠ []) :
  ∀ x ∈ xs, x ≤ (sort xs).get ⟨(sort xs).length - 1, by sorry⟩ := sorry

theorem sort_singleton {α : Type} [Ord α] (x : α) :
  sort [x] = [x] := sorry
-- </vc-theorems>