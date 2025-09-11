-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alternate_sort (lst : List Int) : List Int := sorry

theorem alternate_sort_maintains_elements (lst : List Int) :
  List.length (alternate_sort lst) = List.length lst ∧
  ∀ x, List.count x (alternate_sort lst) = List.count x lst := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: [-3, 2, -4, 5, -9, 8, -42]
-/
-- #guard_msgs in
-- #eval alternate_sort [5, -42, 2, -3, -4, 8, -9]

/-
info: [2, 3, 4, 5, 8, 9]
-/
-- #guard_msgs in
-- #eval alternate_sort [5, 2, 9, 3, 8, 4]

/-
info: [-2, 0, -5, 3, -8, 4, -9]
-/
-- #guard_msgs in
-- #eval alternate_sort [-5, -2, 3, 4, -8, 0, -9]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible