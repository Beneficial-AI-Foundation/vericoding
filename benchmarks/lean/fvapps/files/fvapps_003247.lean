-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_list (xs : List α) : List α := sorry

theorem reverse_list_length {α : Type} (xs : List α) : 
  List.length (reverse_list xs) = List.length xs := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_list_twice {α : Type} (xs : List α) : 
  reverse_list (reverse_list xs) = xs := sorry

theorem reverse_list_preserves_membership {α : Type} (xs : List α) (a : α) :
  a ∈ xs ↔ a ∈ reverse_list xs := sorry

theorem reverse_list_empty {α : Type} :
  reverse_list ([] : List α) = [] := sorry
-- </vc-theorems>