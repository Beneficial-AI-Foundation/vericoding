-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_frog_jumps (s : String) : Nat :=
  sorry

def String.reverse (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem frog_jumps_positive_bound (s : String) :
  solve_frog_jumps s ≥ 1 :=
sorry

theorem frog_jumps_upper_bound (s : String) :
  solve_frog_jumps s ≤ s.length + 2 :=
sorry

theorem frog_jumps_consecutive_r (s : String) :
  solve_frog_jumps s = solve_frog_jumps (s.replace "R" "RR") :=
sorry
-- </vc-theorems>