-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_by_height (a : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_by_height_length {a : List Int} :
  List.length (sort_by_height a) = List.length a :=
  sorry

theorem sort_by_height_trees_unchanged {a : List Int} :
  ∀ i, i < List.length a → (a.get ⟨i, sorry⟩ = -1 ↔ (sort_by_height a).get ⟨i, sorry⟩ = -1) :=
  sorry

theorem sort_by_height_non_trees_sorted {a : List Int} :
  let non_trees := (sort_by_height a).filterMap (fun x => if x = -1 then none else some x)
  ∀ i j, i < j → j < List.length non_trees → 
    non_trees.get ⟨i, sorry⟩ ≤ non_trees.get ⟨j, sorry⟩ :=
  sorry

theorem sort_by_height_same_non_trees {a : List Int} :
  let f := fun x => if x = -1 then none else some x
  List.filterMap f a = List.filterMap f (sort_by_height a) :=
  sorry

theorem sort_by_height_all_trees {a : List Int} :
  (∀ x ∈ a, x = -1) → sort_by_height a = a :=
  sorry

theorem sort_by_height_no_trees {a : List Int} :
  (∀ x ∈ a, x ≠ -1) → 
  ∀ i j, i < j → j < List.length a → 
    (sort_by_height a).get ⟨i, sorry⟩ ≤ (sort_by_height a).get ⟨j, sorry⟩ :=
  sorry
-- </vc-theorems>