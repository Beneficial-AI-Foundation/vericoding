-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Coord := Int × Int

def find_missing_vertex (n : Int) (points : List Coord) : Coord :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_missing_vertex_returns_coordinate_pair (n : Int) (points : List Coord)
  (h1 : 1 ≤ n) (h2 : n ≤ 100) 
  (h3 : 3 ≤ points.length) (h4 : points.length ≤ 10) :
  let result := find_missing_vertex n points
  ∃ x y : Int, result = (x, y) := by sorry

/-
info: (2, 2)
-/
-- #guard_msgs in
-- #eval find_missing_vertex 2 [(1, 1), (1, 2), (4, 6), (2, 1), (9, 6), (9, 3), (4, 3)]

/-
info: (1, 0)
-/
-- #guard_msgs in
-- #eval find_missing_vertex 1 [(0, 0), (0, 1), (1, 1)]

/-
info: (10, 5)
-/
-- #guard_msgs in
-- #eval find_missing_vertex 1 [(5, 5), (5, 10), (10, 10)]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded