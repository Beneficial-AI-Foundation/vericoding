-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flatten {α : Type} (lst : List (NestedList α)) : List α := sorry

theorem flatten_preserves_elements {α : Type} (lst : List (NestedList α)) :
  ∀ x ∈ lst, match x with
  | NestedList.elem v => v ∈ flatten lst
  | NestedList.list xs => ∀ y ∈ xs, match y with 
    | NestedList.elem v => v ∈ flatten lst
    | _ => True := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flatten_removes_one_level {α : Type} (lst : List (NestedList α)) :
  ∀ x ∈ lst, match x with
  | NestedList.list xs => ∀ y ∈ xs, y ≠ NestedList.list []
  | _ => True →
  ∀ z ∈ flatten lst, ∀ w, z ≠ w := sorry

theorem flatten_order_preserved {α : Type} (lst : List (NestedList α)) :
  flatten lst = lst.foldl (λ acc x => 
    match x with
    | NestedList.elem v => acc ++ [v]
    | NestedList.list xs => acc ++ flatten xs
  ) [] := sorry

theorem flatten_identity_flat_list {α : Type} (lst : List α) :
  flatten (lst.map NestedList.elem) = lst := sorry

/-
info: [1, 2, 3, 4, 5, 6]
-/
-- #guard_msgs in
-- #eval flatten [[1, 2, 3], [4, 5, 6]]

/-
info: [1, 2, 'a', 3, 4]
-/
-- #guard_msgs in
-- #eval flatten [[1, 2], "a", [3, 4]]

/-
info: [[1, 2], 3, 4, 5]
-/
-- #guard_msgs in
-- #eval flatten [[[1, 2]], [3, 4], 5]
-- </vc-theorems>