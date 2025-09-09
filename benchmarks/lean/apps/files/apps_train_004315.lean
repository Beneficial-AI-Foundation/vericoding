-- <vc-helpers>
-- </vc-helpers>

def rankings (arr : List Int) : List Nat :=
  sorry

theorem rankings_length {arr : List Int} (h : arr ≠ []) :
  (rankings arr).length = arr.length :=
sorry

theorem rankings_range {arr : List Int} (h : arr ≠ []) :
  let ranks := rankings arr 
  (∀ r ∈ ranks, 1 ≤ r ∧ r ≤ arr.length) ∧ 
  (ranks.length = arr.length) :=
sorry

/-
info: [3, 1, 2]
-/
-- #guard_msgs in
-- #eval rankings [1, 3, 2]

/-
info: [5, 4, 3, 2, 1]
-/
-- #guard_msgs in
-- #eval rankings [1, 2, 3, 4, 5]

/-
info: [5, 4, 6, 7, 1, 9, 10, 2, 8, 3]
-/
-- #guard_msgs in
-- #eval rankings [22, 33, 18, 9, 110, 4, 1, 88, 6, 50]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible