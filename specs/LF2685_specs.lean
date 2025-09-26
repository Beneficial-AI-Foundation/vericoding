-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def duplicates {α : Type u} [BEq α] (arr : List α) : List α := sorry

theorem duplicates_contains_only_duplicated_elements {α : Type u} [BEq α] (arr : List α) :
  ∀ x ∈ duplicates arr, (arr.count x) ≥ 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem duplicates_contains_all_duplicated_elements {α : Type u} [BEq α] (arr : List α) :
  ∀ x, (arr.count x) ≥ 2 → x ∈ duplicates arr := sorry

theorem duplicates_result_has_no_duplicates {α : Type u} [BEq α] (arr : List α) :
  ∀ x ∈ duplicates arr, (duplicates arr).count x = 1 := sorry

theorem duplicates_empty_for_unique {α : Type u} [BEq α] (arr : List α) :
  (∀ x ∈ arr, arr.count x = 1) → duplicates arr = [] := sorry
-- </vc-theorems>