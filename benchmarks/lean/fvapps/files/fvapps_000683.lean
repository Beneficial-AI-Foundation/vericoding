-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def will_pipe_burst (m : Nat) (tc : Int) (th : Int) : String := sorry

theorem pipe_burst_binary_result (m : Nat) (tc th : Int) :
  will_pipe_burst m tc th = "Yes" ∨ will_pipe_burst m tc th = "No" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pipe_burst_temp_not_div_three (m : Nat) (tc th : Int) :
  (th - tc) % 3 ≠ 0 → will_pipe_burst m tc th = "Yes" := sorry

theorem pipe_burst_temp_div_three (m : Nat) (tc th : Int) :
  (th - tc) % 3 = 0 →
  will_pipe_burst m tc th = (if ((th - tc) / 3) ≤ m then "No" else "Yes") := sorry

theorem pipe_no_burst_equal_temps (m : Nat) (t : Int) :
  will_pipe_burst m t t = "No" := sorry
-- </vc-theorems>