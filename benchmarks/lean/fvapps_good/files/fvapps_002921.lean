-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def growing_plant (up_speed : Int) (down_speed : Int) (desired_height : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem growing_plant_result_positive
  (up_speed : Int) (down_diff : Int) (desired_height : Int)
  (h1 : up_speed > 0) (h2 : up_speed ≤ 1000)
  (h3 : down_diff ≥ 0) (h4 : down_diff ≤ 999)
  (h5 : desired_height > 0) (h6 : desired_height ≤ 10000) :
  let down_speed := max 0 (up_speed - down_diff - 1)
  growing_plant up_speed down_speed desired_height ≥ 1 :=
sorry

theorem growing_plant_meets_height
  (up_speed : Int) (down_diff : Int) (desired_height : Int)
  (h1 : up_speed > 0) (h2 : up_speed ≤ 1000)
  (h3 : down_diff ≥ 0) (h4 : down_diff ≤ 999)
  (h5 : desired_height > 0) (h6 : desired_height ≤ 10000) :
  let down_speed := max 0 (up_speed - down_diff - 1)
  let result := growing_plant up_speed down_speed desired_height
  up_speed * result - down_speed * (result - 1) ≥ desired_height :=
sorry
-- </vc-theorems>