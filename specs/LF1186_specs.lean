-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>