-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def two_by_two (animals : List String) : Option (List (String × Nat)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem two_by_two_empty_list :
  two_by_two [] = none := sorry

theorem two_by_two_values_are_two (animals : List String) (result : List (String × Nat)) :
  two_by_two animals = some result →
  ∀ x ∈ result, x.2 = 2 := sorry

theorem two_by_two_keys_appear_multiple_times (animals : List String) (result : List (String × Nat)) :
  two_by_two animals = some result →
  ∀ k ∈ result.map Prod.fst, 
    (animals.filter (· = k)).length > 1 := sorry

theorem two_by_two_contains_all_duplicates (animals : List String) (result : List (String × Nat)) :
  two_by_two animals = some result →
  ∀ k ∈ animals, 
    (animals.filter (· = k)).length > 1 →
    k ∈ result.map Prod.fst := sorry

theorem two_by_two_keys_subset_input (animals : List String) (result : List (String × Nat)) :
  two_by_two animals = some result →
  ∀ k ∈ result.map Prod.fst, k ∈ animals := sorry
-- </vc-theorems>