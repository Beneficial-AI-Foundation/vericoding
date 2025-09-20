-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_temp_difference (today_high today_low normal_high normal_low : Int) : String :=
sorry

def String.contains? (s : String) (substr : String) : Bool :=
sorry

def String.toFloat (s : String) : Float :=
sorry

def Int.toFloat (i : Int) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem temp_diff_result_format (today_high today_low normal_high normal_low : Int)
  (h1 : today_high ≥ today_low) (h2 : normal_high ≥ normal_low) :
  let result := calculate_temp_difference today_high today_low normal_high normal_low
  ∃ (diff : String) (dir : String),
    result = diff ++ " DEGREE(S) " ++ dir ++ " NORMAL" ∧
    (dir = "ABOVE" ∨ dir = "BELOW") :=
sorry

theorem temp_diff_nonnegative (today_high today_low normal_high normal_low : Int)
  (h1 : today_high ≥ today_low) (h2 : normal_high ≥ normal_low) :
  let result := calculate_temp_difference today_high today_low normal_high normal_low
  let parts := result.splitOn " DEGREE(S) "
  let diff := parts[0]!
  String.toFloat diff ≥ 0 :=
sorry

theorem temp_diff_direction (today_high today_low normal_high normal_low : Int)
  (h1 : today_high ≥ today_low) (h2 : normal_high ≥ normal_low) :
  let result := calculate_temp_difference today_high today_low normal_high normal_low
  let avg_today : Float := (today_high.toFloat + today_low.toFloat) / 2
  let avg_normal : Float := (normal_high.toFloat + normal_low.toFloat) / 2
  (avg_today > avg_normal → result.contains? "ABOVE") ∧
  (avg_today ≤ avg_normal → result.contains? "BELOW") :=
sorry
-- </vc-theorems>