-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findCloserTruck (coords : List Int) : String := sorry

theorem find_closer_truck_output_valid (coords : List Int) 
  (h : coords.length = 4) : 
  (findCloserTruck coords = "A IS CLOSER") ∨ 
  (findCloserTruck coords = "B IS CLOSER") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equal_distance_returns_a (x y : Int) :
  findCloserTruck [x, y, x, y] = "A IS CLOSER" := sorry

theorem symmetric_distance (x y : Int) (h : 0 ≤ x ∧ 0 ≤ y) :
  let coords1 := [x, y, x+1, y+1]
  let coords2 := [-x, y, -(x+1), y+1]
  let coords3 := [-x, -y, -(x+1), -(y+1)]
  let coords4 := [x, -y, x+1, -(y+1)]
  findCloserTruck coords1 = findCloserTruck coords2 ∧
  findCloserTruck coords2 = findCloserTruck coords3 ∧
  findCloserTruck coords3 = findCloserTruck coords4 := sorry
-- </vc-theorems>