-- <vc-helpers>
-- </vc-helpers>

def findCloserTruck (coords : List Int) : String := sorry

theorem find_closer_truck_output_valid (coords : List Int) 
  (h : coords.length = 4) : 
  (findCloserTruck coords = "A IS CLOSER") ∨ 
  (findCloserTruck coords = "B IS CLOSER") := sorry

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

/-
info: 'A IS CLOSER'
-/
-- #guard_msgs in
-- #eval find_closer_truck [3, -2, -5, -3]

/-
info: 'B IS CLOSER'
-/
-- #guard_msgs in
-- #eval find_closer_truck [0, 6, 1, 2]

/-
info: 'B IS CLOSER'
-/
-- #guard_msgs in
-- #eval find_closer_truck [-7, 8, 4, -1]

-- Apps difficulty: interview
-- Assurance level: unguarded