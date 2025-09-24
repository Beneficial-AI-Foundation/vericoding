-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_time (battery : Float) (charger : Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_time_known_value :
    (calculate_time 1000 500 - 2.6).abs < 0.01 :=
    sorry
-- </vc-theorems>