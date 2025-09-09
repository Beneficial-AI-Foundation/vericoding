-- <vc-helpers>
-- </vc-helpers>

def calculate_time (battery : Float) (charger : Float) : Float :=
  sorry

theorem calculate_time_known_value :
    (calculate_time 1000 500 - 2.6).abs < 0.01 :=
    sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible