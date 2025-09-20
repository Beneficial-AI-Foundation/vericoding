-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sabb (s : String) (value happiness : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sabb_zero_inputs_fails_when_string_short {s : String}
  (h : s.length ≤ 22) : sabb s 0 0 = "Back to your desk, boy." := 
sorry

theorem sabb_empty_string_succeeds_when_scores_high {value happiness : Nat}
  (h : value + happiness > 22) : sabb "" value happiness = "Sabbatical! Boom!" :=
sorry

theorem sabb_empty_string_fails_when_scores_low {value happiness : Nat}
  (h : value + happiness ≤ 22) : sabb "" value happiness = "Back to your desk, boy." :=
sorry
-- </vc-theorems>