-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_gem_game (n m : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_gem_game_nonneg (n m : Nat) :
  solve_gem_game n m ≥ 0 :=
sorry

theorem solve_gem_game_m_one (n : Nat) :
  solve_gem_game n 1 = if n % 2 = 0 then n/2 else n/2 + 1 :=
sorry

theorem solve_gem_game_large_m (n m : Nat) (h : m > (n+1)/2) :
  solve_gem_game n m = m :=
sorry
-- </vc-theorems>