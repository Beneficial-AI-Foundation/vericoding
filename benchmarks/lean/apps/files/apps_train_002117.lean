-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_xorinacci (a b n : Nat) : Nat := sorry

theorem xorinacci_cycle (a b n : Nat) :
  solve_xorinacci a b n = solve_xorinacci a b (n + 3) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem xorinacci_initial_zero (a b : Nat) :
  solve_xorinacci a b 0 = a := sorry

theorem xorinacci_initial_one (a b : Nat) :
  solve_xorinacci a b 1 = b := sorry

theorem xorinacci_xor_commutative (a b : Nat) :
  solve_xorinacci a b 2 = solve_xorinacci b a 2 := sorry

theorem xorinacci_xor_with_zero (x : Nat) :
  solve_xorinacci x 0 2 = x := sorry

theorem xorinacci_zero_xor (x : Nat) :
  solve_xorinacci 0 x 2 = x := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_xorinacci 3 4 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_xorinacci 4 5 0

/-
info: 76
-/
-- #guard_msgs in
-- #eval solve_xorinacci 325 265 1231232
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible