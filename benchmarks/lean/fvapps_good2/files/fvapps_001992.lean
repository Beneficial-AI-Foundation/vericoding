-- <vc-preamble>
def MOD : Nat := 998244353
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_biscuit_game (n : Nat) (biscuits : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_range (n : Nat) (biscuits : List Nat) :
  n > 0 → 0 ≤ solve_biscuit_game n biscuits ∧ solve_biscuit_game n biscuits < MOD :=
sorry

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
-- </vc-theorems>