-- <vc-preamble>
def solve_biscuit_game (n : Nat) (biscuits : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Nat := 998244353

theorem output_range (n : Nat) (biscuits : List Nat) :
  n > 0 → 0 ≤ solve_biscuit_game n biscuits ∧ solve_biscuit_game n biscuits < MOD :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_biscuits (n : Nat) (len : Nat) : 
  n > 0 → solve_biscuit_game n (List.replicate len 0) = 0 :=
sorry

theorem equal_distribution (n : Nat) (biscuits : List Nat) :
  n > 0 → biscuits ≠ [] →
  0 ≤ solve_biscuit_game n (List.replicate biscuits.length (List.head! biscuits)) ∧
  solve_biscuit_game n (List.replicate biscuits.length (List.head! biscuits)) < MOD :=
sorry

theorem single_player (n : Nat) (biscuits : List Nat) :
  n = 1 → biscuits ≠ [] → solve_biscuit_game n biscuits = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_biscuit_game 2 [1, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_biscuit_game 2 [1, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_biscuit_game 5 [0, 0, 0, 0, 35]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded