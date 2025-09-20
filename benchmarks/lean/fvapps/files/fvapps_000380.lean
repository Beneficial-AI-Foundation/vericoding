-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_alice_win_stones (n : Nat) : Bool := sorry

theorem always_returns_bool (n : Nat) (h : n > 0) :
  ∃ b : Bool, can_alice_win_stones n = b :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem perfect_squares_winnable (n : Nat) (h₁ : n > 0) (h₂ : ∃ k, n = k * k) :
  can_alice_win_stones n = true :=
sorry

theorem two_stones_loses :
  can_alice_win_stones 2 = false :=
sorry

theorem removing_squares_possible (n : Nat) (h₁ : n > 0) (h₂ : ∃ k : Nat, n = k * k) :
  can_alice_win_stones n = true :=
sorry

theorem large_inputs_return_bool (n : Nat) (h₁ : n ≥ 1000) (h₂ : n ≤ 10000) :
  ∃ b : Bool, can_alice_win_stones n = b :=
sorry
-- </vc-theorems>