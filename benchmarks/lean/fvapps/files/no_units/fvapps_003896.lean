-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def filter_list {α : Type} (lst : List α) : List α := sorry

theorem filter_list_removes_strings (lst : List (Int ⊕ String)) :
  let result := filter_list lst
  (∀ x ∈ result, (∃ n : Int, x = Sum.inl n)) ∧
  (∀ x ∈ result, x ∈ lst) ∧
  (List.length result = List.length (List.filter (fun x => match x with
    | Sum.inl _ => true
    | Sum.inr _ => false) lst)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem filter_list_preserves_numbers_only (lst : List Int) :
  filter_list lst = lst := sorry

theorem filter_list_removes_all_strings (lst : List String) :
  filter_list lst = [] := sorry

theorem filter_list_maintains_order (lst : List Int) :
  filter_list lst = lst := sorry
-- </vc-theorems>