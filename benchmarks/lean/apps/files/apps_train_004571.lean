def List.Sorted {α : Type} (r : α → α → Prop) (l : List α) : Prop :=
  ∀ i j, i < j → j < l.length → r (l.get ⟨i, sorry⟩) (l.get ⟨j, sorry⟩)

structure Result where
  i : Nat
  n : Int

-- <vc-helpers>
-- </vc-helpers>

def all_non_consecutive (arr : List Int) : List Result :=
  sorry

theorem consecutive_not_in_result (arr : List Int) (h : arr.length ≥ 2) :
  ∀ i, i < arr.length - 1 →
  arr.get ⟨i+1, sorry⟩ = arr.get ⟨i, sorry⟩ + 1 →
  ¬∃ r ∈ all_non_consecutive arr, r.i = i + 1 :=
sorry

theorem non_consecutive_in_result (arr : List Int) (h : arr.length ≥ 2) :
  ∀ i, i < arr.length - 1 →
  arr.get ⟨i+1, sorry⟩ ≠ arr.get ⟨i, sorry⟩ + 1 →
  ∃ r ∈ all_non_consecutive arr, r.i = i + 1 ∧ r.n = arr.get ⟨i+1, sorry⟩ :=
sorry

theorem indices_ascending (arr : List Int) (h : arr.length ≥ 2) :
  let result := all_non_consecutive arr
  result.length > 1 →
  List.Sorted (·≤·) (result.map Result.i) :=
sorry

theorem valid_indices (arr : List Int) (h : arr.length ≥ 2) :
  ∀ r ∈ all_non_consecutive arr,
  1 ≤ r.i ∧ r.i < arr.length :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval all_non_consecutive [1, 2, 3, 4, 6, 7, 8, 15, 16]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval all_non_consecutive [1, 2, 3, 4, 5]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval all_non_consecutive [-3, -2, -1, 1, 2, 4, 5]

-- Apps difficulty: introductory
-- Assurance level: unguarded