-- <vc-helpers>
-- </vc-helpers>

def sort_array (xs : List Int) : List Int :=
  sorry

theorem sort_array_maintains_length (xs : List Int) :
  (sort_array xs).length = xs.length :=
sorry

theorem sort_array_perm (xs : List Int) :
  List.Perm xs (sort_array xs) :=
sorry

theorem sort_array_pure (xs : List Int) :
  sort_array xs = sort_array xs :=
sorry

theorem sort_array_empty_list :
  sort_array [] = [] :=
sorry

/-
info: [1, 2, 3, 5]
-/
-- #guard_msgs in
-- #eval sort_array [5, 2, 3, 1]

/-
info: [0, 0, 1, 1, 2, 5]
-/
-- #guard_msgs in
-- #eval sort_array [5, 1, 1, 2, 0, 0]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval sort_array [1]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible