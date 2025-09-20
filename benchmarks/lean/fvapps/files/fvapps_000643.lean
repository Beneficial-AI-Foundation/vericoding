-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MODULO := 1000000007

def sum_odds_in_range (l r : Nat) : Nat :=
  sorry

def solve_alternate_odd_sum (d l r : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_non_negative (d l r : Nat) :
  solve_alternate_odd_sum d l r ≥ 0 :=
sorry

theorem same_start_end_even (d l : Nat) :
  l % 2 = 0 →
  solve_alternate_odd_sum d l l = 0 :=
sorry

theorem empty_range (d : Nat) :
  ∀ l r : Nat, r < l →
  solve_alternate_odd_sum d l r = 0 :=
sorry
-- </vc-theorems>