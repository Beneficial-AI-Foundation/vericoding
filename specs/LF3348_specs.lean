-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compound_array {α : Type} [DecidableEq α] (a b : List α) : List α := sorry

theorem compound_array_length {α : Type} [DecidableEq α] (a b : List α) :
  (compound_array a b).length = a.length + b.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compound_array_preserves_elements {α : Type} [DecidableEq α] (a b : List α) (x : α) :
  (x ∈ a ∨ x ∈ b) ↔ x ∈ compound_array a b := sorry

theorem compound_array_maintains_relative_order {α : Type} [DecidableEq α] (a b : List α) :
  ∀ i j x y, i < j →
    ((x ∈ a ∧ y ∈ a) → 
      (List.get (compound_array a b) i = x ∧ List.get (compound_array a b) j = y) → 
      ∃ i' j', List.get a i' = x ∧ List.get a j' = y ∧ i' < j') ∧
    ((x ∈ b ∧ y ∈ b) → 
      (List.get (compound_array a b) i = x ∧ List.get (compound_array a b) j = y) → 
      ∃ i' j', List.get b i' = x ∧ List.get b j' = y ∧ i' < j') := sorry

theorem compound_array_empty_list {α : Type} [DecidableEq α] (a : List α) :
  compound_array a [] = a ∧ 
  compound_array [] a = a := sorry

theorem compound_array_empty_both {α : Type} [DecidableEq α] :
  compound_array ([] : List α) [] = [] := sorry
-- </vc-theorems>