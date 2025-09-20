-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_last_laddu (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_last_laddu_bounds (n : Nat) (h : n > 0) : 
  let result := find_last_laddu n
  0 < result ∧ result ≤ n := 
sorry

theorem find_last_laddu_next_power_exceeds (n : Nat) (h : n > 0) :
  let result := find_last_laddu n
  2 * result > n :=
sorry
-- </vc-theorems>