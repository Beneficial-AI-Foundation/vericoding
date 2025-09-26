-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def what_time_is_it (angle : Float) : String :=
sorry

def str_to_hours_mins (s : String) : Nat × Nat :=
sorry

def angle_to_total_mins (angle : Float) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem time_format_valid {angle : Float} (h : 0 ≤ angle ∧ angle ≤ 360) :
  let result := what_time_is_it angle
  let (hours, mins) := str_to_hours_mins result
  result.length = 5 ∧
  hours ≥ 1 ∧ hours ≤ 12 ∧
  mins ≥ 0 ∧ mins ≤ 59 :=
sorry

theorem time_calculation_consistent {angle : Float} (h : 0 ≤ angle ∧ angle ≤ 360) :
  let result := what_time_is_it angle
  let (hours, mins) := str_to_hours_mins result
  let expected_total_mins := angle / 360 * 12 * 60
  let actual_total_mins := (hours % 12) * 60 + mins
  (expected_total_mins - actual_total_mins.toFloat).abs < 2 :=
sorry

theorem hour_boundaries_correct (angle : Nat) (h : angle < 360) :
  let result := what_time_is_it angle.toFloat
  let (hours, _) := str_to_hours_mins result
  if angle < 30 then hours = 12
  else hours = angle / 30 :=
sorry

theorem specific_angles_correct :
  (str_to_hours_mins (what_time_is_it 0)).1 = 12 ∧
  (str_to_hours_mins (what_time_is_it 30)).1 = 1 ∧
  (str_to_hours_mins (what_time_is_it 330)).1 = 11 :=
sorry
-- </vc-theorems>