-- <vc-helpers>
-- </vc-helpers>

def Car := Float × Float

def freeway_game (km : Float) (kph : Float) (cars : List Car) : Int :=
  sorry

theorem freeway_game_properties (km : Float) (kph : Float) (cars : List Car)
  (h1 : 0.1 ≤ km ∧ km ≤ 1000)  
  (h2 : 1 ≤ kph ∧ kph ≤ 200) :
  let result := freeway_game km kph cars
  -- Result score cannot exceed number of cars 
  (Int.natAbs result ≤ cars.length) ∧ 
  -- With no cars, score should be 0
  (cars = [] → result = 0)
  := sorry

theorem speed_relationship (km : Float) (kph : Float) (cars : List Car)
  (h1 : 0.1 ≤ km ∧ km ≤ 1000)
  (h2 : 1 ≤ kph ∧ kph ≤ 200) :
  let result_slow := freeway_game km 60 cars
  let result_fast := freeway_game km 180 cars
  cars ≠ [] → result_slow ≤ result_fast
  := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval freeway_game 50.0 130.0 [[-1.0, 120.0], [-1.5, 120.0]]

/-
info: -2
-/
-- #guard_msgs in
-- #eval freeway_game 50.0 110.0 [[1.0, 120.0], [1.5, 125.0]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval freeway_game 50.0 120.0 [[-1.0, 115.0], [-1.5, 110.0], [1.0, 130.0], [1.5, 130.0]]

-- Apps difficulty: introductory
-- Assurance level: unguarded