-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def car_fleet (target: Int) (positions: List Int) (speeds: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem car_fleet_bounded (target: Int) (positions: List Int) (speeds: List Int)
  (h1: target > 0) (h2: target ≤ 1000)
  (h3: ∀ p ∈ positions, 0 ≤ p ∧ p ≤ 100)
  (h4: ∀ s ∈ speeds, 1 ≤ s ∧ s ≤ 10)
  (h5: positions.length = speeds.length)
  (h6: positions.length ≤ 10) :
  car_fleet target positions speeds ≤ positions.length :=
sorry

theorem car_fleet_empty (target: Int) :
  car_fleet target [] [] = 0 :=
sorry

theorem car_fleet_single (target: Int) (pos: Int) (speed: Int)
  (h1: target > 0) :
  car_fleet target [pos] [speed] = 1 :=
sorry

theorem car_fleet_same_pos_speed (target: Int) (positions: List Int) (speeds: List Int)
  (h1: positions ≠ [])
  (h2: ∀ p ∈ positions, p = positions.head!)
  (h3: ∀ s ∈ speeds, s = speeds.head!)
  (h4: positions.length = speeds.length) :
  car_fleet target positions speeds = 1 :=
sorry

theorem car_fleet_merge_same_pos (target: Int)
  (h1: target = 10) :
  car_fleet 10 [5, 5] [2, 3] = 1 :=
sorry

theorem car_fleet_no_merge_separated (target: Int) 
  (h1: target = 10) :
  car_fleet 10 [0, 5] [1, 2] = 2 :=
sorry
-- </vc-theorems>