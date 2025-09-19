-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_moving_soldiers (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string :
  solve_moving_soldiers "" = 0 :=
sorry

theorem all_zeros (n : Nat) :
  solve_moving_soldiers (String.mk (List.replicate n '0')) = 0 :=
sorry

theorem all_ones (n : Nat) :
  solve_moving_soldiers (String.mk (List.replicate n '1')) = 0 :=
sorry

theorem trailing_ones_invariant (s₁ s₂ : String) :
  s₂ = s₁ ++ String.mk (List.replicate 3 '1') →
  solve_moving_soldiers s₁ = solve_moving_soldiers s₂ :=
sorry

theorem result_nonnegative (s : String) :
  solve_moving_soldiers s ≥ 0 :=
sorry

theorem no_movement_needed (s : String) :
  (s.toList.filter (· = '1')).length = 0 ∨
  (s.toList.dropWhile (· = '1')).isEmpty →
  solve_moving_soldiers s = 0 :=
sorry
-- </vc-theorems>