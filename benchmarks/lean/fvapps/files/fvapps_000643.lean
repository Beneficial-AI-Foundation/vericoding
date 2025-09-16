-- <vc-preamble>
def MODULO := 1000000007

def sum_odds_in_range (l r : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
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

/-
info: 114
-/
-- #guard_msgs in
-- #eval solve_alternate_odd_sum 3 10 33

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_alternate_odd_sum 2 1 7

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_alternate_odd_sum 3 1 9
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible