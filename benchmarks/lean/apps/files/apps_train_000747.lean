-- <vc-preamble>
def find_rectangle_areas (n : Nat) (numbers : List Nat) : Nat × Nat := sorry

theorem find_rectangle_areas_ordering
  (numbers : List Nat)
  (h : numbers.length ≥ 2) :
  let (max_area, min_area) := find_rectangle_areas numbers.length numbers
  max_area ≥ min_area :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximumTwoProduct (l : List Nat) : Nat := sorry
def minimumTwoProduct (l : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_rectangle_areas_minimal
  (numbers : List Nat)
  (h : numbers = [1, 1]) :
  find_rectangle_areas 2 numbers = (1, 1) :=
sorry

theorem find_rectangle_areas_preserves_input
  (numbers : List Nat)
  (h : numbers.length ≥ 2) :
  let original := numbers
  let _ := find_rectangle_areas numbers.length numbers
  numbers = original :=
sorry

/-
info: (20, 2)
-/
-- #guard_msgs in
-- #eval find_rectangle_areas 5 [4, 2, 1, 5, 3]

/-
info: (12, 2)
-/
-- #guard_msgs in
-- #eval find_rectangle_areas 4 [1, 2, 3, 4]

/-
info: (30, 2)
-/
-- #guard_msgs in
-- #eval find_rectangle_areas 6 [5, 4, 3, 2, 1, 6]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible