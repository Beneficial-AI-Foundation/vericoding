-- <vc-preamble>
def MOD : Nat := 1000000007
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_zombie_cars (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_zombie_cars_output_range (n k : Nat) :
  n ≥ 1 → k ≥ 1 → solve_zombie_cars n k < MOD :=
sorry

theorem solve_zombie_cars_k_one (n k : Nat) :
  n ≥ 1 → k = 1 → solve_zombie_cars n k = if n = 1 then 1 else 0 :=
sorry

theorem solve_zombie_cars_formula (n k : Nat) :
  n ≥ 1 → k ≥ 1 →
  solve_zombie_cars n k = (k * (k-1)^(n-1)) % MOD :=
sorry

theorem solve_zombie_cars_known_values :
  solve_zombie_cars 2 2 = 2 ∧
  solve_zombie_cars 3 3 = 12 ∧
  solve_zombie_cars 4 3 = 24 :=
sorry
-- </vc-theorems>