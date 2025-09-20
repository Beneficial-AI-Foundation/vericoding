-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_subarrays (n : Nat) (arr : List Nat) : Nat :=
sorry

def count_valid_subarrays (n : Nat) (arr : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_subarrays_singleton (x : Nat) :
  solve_subarrays 1 [x] = 0 :=
sorry

theorem solve_subarrays_alternating_nonneg (n : Nat) :
  let arr := List.replicate (2*n) 100000000 ++ List.replicate (2*n) 900000000
  solve_subarrays (4*n) arr ≥ 0 :=
sorry
-- </vc-theorems>