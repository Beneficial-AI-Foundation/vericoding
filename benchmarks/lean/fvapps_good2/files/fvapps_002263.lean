-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_moves_required (n : Nat) : Nat :=
  sorry

def nat_sqrt (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_moves_non_negative (n : Nat) (h : n > 0) :
  min_moves_required n ≥ 0 :=
sorry

theorem min_moves_less_than_input (n : Nat) (h : n > 0) :
  min_moves_required n ≤ n :=
sorry

theorem min_moves_monotonic (n : Nat) (h : n > 1) :
  min_moves_required n ≥ min_moves_required (n-1) :=
sorry

theorem min_moves_base_case :
  min_moves_required 1 = 0 :=
sorry
-- </vc-theorems>