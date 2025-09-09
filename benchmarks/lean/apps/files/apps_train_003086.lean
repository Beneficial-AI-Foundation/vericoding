-- <vc-helpers>
-- </vc-helpers>

def sort_by_height (a : List Int) : List Int :=
  sorry

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

/-
info: expected1
-/
-- #guard_msgs in
-- #eval sort_by_height [-1, 150, 190, 170, -1, -1, 160, 180]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval sort_by_height [-1, -1, -1, -1, -1]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval sort_by_height [4, 2, 9, 11, 2, 16]

-- Apps difficulty: introductory
-- Assurance level: unguarded