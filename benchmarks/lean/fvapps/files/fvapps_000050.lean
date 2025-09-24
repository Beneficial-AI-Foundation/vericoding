-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_jams (n : Nat) (jams : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_jams_non_negative (n : Nat) (jams : List Nat) :
  n > 0 → jams.length = 2*n → solve_jams n jams ≥ 0 :=
sorry

theorem solve_jams_upper_bound (n : Nat) (jams : List Nat) :
  n > 0 → jams.length = 2*n → solve_jams n jams ≤ 2*n :=
sorry

theorem solve_jams_all_ones (n : Nat) :
  n > 0 → solve_jams n (List.replicate (2*n) 1) = 2*n :=
sorry
-- </vc-theorems>