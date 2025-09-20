-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Car := Float × Float

def freeway_game (km : Float) (kph : Float) (cars : List Car) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>