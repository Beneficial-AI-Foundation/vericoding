-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_score_triangulation (vertices : List Nat) : Nat := sorry

theorem min_score_triangulation_nonnegative (vertices : List Nat) 
  (h: vertices.length ≥ 3) : 
  min_score_triangulation vertices ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_score_triangulation_triangle (a b c : Nat) :
  min_score_triangulation [a, b, c] = a * b * c := sorry

theorem min_score_triangulation_cyclic_invariant (vertices : List Nat) 
  (h: vertices.length ≥ 3) :
  min_score_triangulation vertices = 
  min_score_triangulation (vertices.tail ++ [vertices.head!]) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_score_triangulation [1, 2, 3]

/-
info: 144
-/
-- #guard_msgs in
-- #eval min_score_triangulation [3, 7, 4, 5]

/-
info: 13
-/
-- #guard_msgs in
-- #eval min_score_triangulation [1, 3, 1, 4, 1, 5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded