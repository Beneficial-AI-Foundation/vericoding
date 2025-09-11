-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (l : List Int) : Int := sorry

def min_grass_needed (arr : List Int) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_grass_needed_non_negative (arr : List Int) (h : arr ≠ []) : 
  min_grass_needed arr ≥ 0 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_grass_needed [5, -5]

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_grass_needed [-5, 5]

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_grass_needed [1, 2, -3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible