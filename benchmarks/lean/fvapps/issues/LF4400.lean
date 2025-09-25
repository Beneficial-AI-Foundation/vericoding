-- <vc-preamble>
def List.sum : List Int → Int 
  | [] => 0
  | (x::xs) => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_section_id (scroll : Int) (sizes : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_section_id_bounds (scroll : Int) (sizes : List Int) (h : sizes ≠ []) :
  -1 ≤ get_section_id scroll sizes ∧ get_section_id scroll sizes < sizes.length :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval get_section_id 1 [300, 200, 400, 600, 100]

/-
info: 1
-/
-- #guard_msgs in
-- #eval get_section_id 300 [300, 200, 400, 600, 100]

/-
info: -1
-/
-- #guard_msgs in
-- #eval get_section_id 1600 [300, 200, 400, 600, 100]
-- </vc-theorems>