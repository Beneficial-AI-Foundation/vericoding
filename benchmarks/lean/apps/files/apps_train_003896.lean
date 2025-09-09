-- <vc-helpers>
-- </vc-helpers>

def filter_list {α : Type} (lst : List α) : List α := sorry

theorem filter_list_removes_strings (lst : List (Int ⊕ String)) :
  let result := filter_list lst
  (∀ x ∈ result, (∃ n : Int, x = Sum.inl n)) ∧
  (∀ x ∈ result, x ∈ lst) ∧
  (List.length result = List.length (List.filter (fun x => match x with
    | Sum.inl _ => true
    | Sum.inr _ => false) lst)) := sorry

theorem filter_list_preserves_numbers_only (lst : List Int) :
  filter_list lst = lst := sorry

theorem filter_list_removes_all_strings (lst : List String) :
  filter_list lst = [] := sorry

theorem filter_list_maintains_order (lst : List Int) :
  filter_list lst = lst := sorry

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval filter_list [1, 2, "a", "b"]

/-
info: [1, 0, 15]
-/
-- #guard_msgs in
-- #eval filter_list [1, "a", "b", 0, 15]

/-
info: [1, 2, 123]
-/
-- #guard_msgs in
-- #eval filter_list [1, 2, "aasf", "1", "123", 123]

-- Apps difficulty: introductory
-- Assurance level: guarded