-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (points : List (Nat × Nat)) : List Nat :=
sorry

def sqrt (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_output_length {points : List (Nat × Nat)} :
  points.length = (solve points).length :=
sorry

theorem solve_output_bound {points : List (Nat × Nat)} (i : Fin points.length) :
  let (a, b) := points.get i
  let sqrt_ab := sqrt (a * b)
  ∃ j : Fin (solve points).length, (solve points).get j ≤ 2 * sqrt_ab :=
sorry

theorem solve_output_nonneg {points : List (Nat × Nat)} (i : Fin (solve points).length) :
  0 ≤ (solve points).get i :=
sorry

theorem solve_one_input :
  solve [(1, 1)] = [0] :=
sorry
-- </vc-theorems>