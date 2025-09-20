-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lcm (a b : Nat) : Nat :=
sorry

def gcd (a b : Nat) : Nat :=
sorry

def solve_lovers_lcm (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lcm_self (n : Nat) : lcm n n = n :=
sorry

theorem gcd_self (n : Nat) (h : n > 0) : gcd n n = n :=
sorry

theorem lcm_one (n : Nat) (h : n > 0) : lcm n 1 = n :=
sorry

theorem gcd_one (n : Nat) (h : n > 0) : gcd n 1 = 1 :=
sorry

theorem lcm_comm (a b : Nat) : lcm a b = lcm b a :=
sorry

theorem gcd_comm (a b : Nat) : gcd a b = gcd b a :=
sorry

theorem solve_lovers_valid_output (n : Nat) (h : n > 0) :
  solve_lovers_lcm n = "Nova's gonna kill me" ∨
  solve_lovers_lcm n = "YESS(sunglass emo)" :=
sorry

theorem solve_lovers_deterministic (n : Nat) :
  solve_lovers_lcm n = solve_lovers_lcm n :=
sorry
-- </vc-theorems>