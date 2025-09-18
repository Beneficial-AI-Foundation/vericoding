-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def phi (n : Nat) : Nat :=
  sorry

def solve_passcode (a m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem phi_positive (n : Nat) (h : n > 0) : phi n > 0 :=
sorry

theorem phi_upper_bound (n : Nat) : phi n ≤ n :=
sorry

theorem phi_one : phi 1 = 1 :=
sorry

theorem solve_passcode_positive (a m : Nat) (h₁ : a > 0) (h₂ : m > 0) :
  solve_passcode a m > 0 :=
sorry

theorem solve_passcode_upper_bound (a m : Nat) (h₁ : a > 0) (h₂ : m > 0) :
  solve_passcode a m ≤ m :=
sorry

theorem solve_passcode_one (a : Nat) (h : a > 0) :
  solve_passcode a 1 = 1 :=
sorry

theorem solve_passcode_coprime (a m : Nat) (h₁ : a > 0) (h₂ : m > 0)
  (h₃ : Nat.gcd a m = 1) :
  solve_passcode a m = phi m :=
sorry

theorem solve_passcode_gcd (a m : Nat) (h₁ : a > 0) (h₂ : m > 0) :
  solve_passcode a m = phi (m / Nat.gcd a m) :=
sorry
-- </vc-theorems>