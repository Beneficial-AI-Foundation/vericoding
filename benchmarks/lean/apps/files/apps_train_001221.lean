-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_gem_game (n m : Nat) : Nat := sorry

/- The result of solve_gem_game is never negative -/
-- </vc-definitions>

-- <vc-theorems>
theorem solve_gem_game_nonneg (n m : Nat) :
  solve_gem_game n m ≥ 0 := sorry

/- When m=1, result follows pattern based on n being even/odd -/

theorem solve_gem_game_m_one (n : Nat) :
  solve_gem_game n 1 = if n % 2 = 0 then n/2 else n/2 + 1 := sorry

/- For m > (n+1)/2, result equals m -/

theorem solve_gem_game_large_m (n m : Nat) (h : m > (n+1)/2) :
  solve_gem_game n m = m := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_gem_game 4 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_gem_game 6 3

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_gem_game 10 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded