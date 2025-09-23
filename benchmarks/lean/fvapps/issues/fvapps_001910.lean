-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def carPooling (trips : List Trip) (capacity : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem capacity_zero (trips : List Trip) :
  carPooling trips 0 = (trips.length = 0) :=
  sorry

theorem timeline_under_capacity (trips : List Trip) (capacity : Int) :
  carPooling trips capacity = true →
  ∀ t : Int, 
    (trips.foldl (λ acc trip =>
      if t ≥ trip.startLoc ∧ t < trip.endLoc
      then acc + trip.passengers 
      else acc) 0) ≤ capacity :=
  sorry

theorem large_capacity_always_works (trips : List Trip) :
  carPooling trips 1000000 = true :=
  sorry

theorem timeline_consistency (trips : List Trip) :
  (trips.foldl (λ acc trip => acc + trip.passengers - trip.passengers) 0) = 0 :=
  sorry

theorem trip_valid (t : Trip) : 
  t.passengers > 0 ∧ 
  t.passengers ≤ 1000 ∧ 
  t.startLoc ≥ 0 ∧ 
  t.startLoc < 1000 ∧ 
  t.endLoc > 0 ∧ 
  t.endLoc ≤ 1000 ∧ 
  t.startLoc < t.endLoc :=
  sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval car_pooling [[2, 1, 5], [3, 3, 7]] 4

/-
info: True
-/
-- #guard_msgs in
-- #eval car_pooling [[2, 1, 5], [3, 3, 7]] 5

/-
info: True
-/
-- #guard_msgs in
-- #eval car_pooling [[3, 2, 7], [3, 7, 9], [8, 3, 9]] 11
-- </vc-theorems>