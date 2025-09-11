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

/-
info: [4, 3, 2, 1]
-/
-- #guard_msgs in
-- #eval reverse_list [1, 2, 3, 4]

/-
info: [4, 5, 1, 3]
-/
-- #guard_msgs in
-- #eval reverse_list [3, 1, 5, 4]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval reverse_list [1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible