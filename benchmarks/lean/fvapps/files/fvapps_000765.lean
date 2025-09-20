-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_max_profit_days (A : Nat) : Nat × Nat := sorry

def profit (A D : Nat) : Int := 
  Int.ofNat (A * D) + 1 - Int.ofNat (2^D)
-- </vc-definitions>

-- <vc-theorems>
theorem max_profit_days_non_negative (A : Nat) (h : A ≥ 2) :
  let (D1, D2) := solve_max_profit_days A
  D1 ≥ 0 ∧ D2 ≥ 0 := sorry

theorem max_profit_days_ordered (A : Nat) (h : A ≥ 2) :
  let (D1, D2) := solve_max_profit_days A
  D1 ≥ D2 := sorry

theorem max_profit_days_D2_bound (A : Nat) (h : A ≥ 2) :
  let (D1, D2) := solve_max_profit_days A 
  A ≤ 2^D2 := sorry

theorem max_profit_days_edge_cases :
  solve_max_profit_days 2 = (2, 1) ∧ 
  solve_max_profit_days 3 = (3, 2) ∧
  solve_max_profit_days 4 = (4, 2) := sorry
-- </vc-theorems>