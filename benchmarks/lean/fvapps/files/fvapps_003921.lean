-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cooking_time (needed_power : String) (minutes : Nat) (seconds : Nat) (power : String) : String := sorry

theorem cooking_time_format (needed_power : String) (minutes : Nat) 
  (seconds : Nat) (power : String) (h1 : minutes ≤ 60) (h2 : seconds < 60) :
  ∃ result_mins result_secs : Nat,
    cooking_time needed_power minutes seconds power = 
      s!"{result_mins} minutes {result_secs} seconds" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cooking_time_time_bounds (needed_power : String) (minutes : Nat)
  (seconds : Nat) (power : String) (h1 : minutes ≤ 60) (h2 : seconds < 60) :
  let result := cooking_time needed_power minutes seconds power
  ∃ result_mins result_secs : Nat,
    result = s!"{result_mins} minutes {result_secs} seconds" ∧
    result_secs < 60 ∧ 
    result_mins ≥ 0 := sorry

theorem cooking_time_power_conservation (needed_power : String) (minutes : Nat)
  (seconds : Nat) (power : String) (h1 : minutes ≤ 60) (h2 : seconds < 60) :
  let result := cooking_time needed_power minutes seconds power
  ∃ result_mins result_secs input_watts output_watts : Nat,
    result = s!"{result_mins} minutes {result_secs} seconds" ∧
    input_watts * (minutes * 60 + seconds) ≤ 
    output_watts * (result_mins * 60 + result_secs) + output_watts := sorry

theorem cooking_time_zero :
  cooking_time "100W" 0 0 "100W" = "0 minutes 0 seconds" := sorry

theorem cooking_time_same_power :
  cooking_time "800W" 5 30 "800W" = "5 minutes 30 seconds" := sorry
-- </vc-theorems>