-- <vc-helpers>
-- </vc-helpers>

def MOD := 1000000007

def solve_nice_integers (a b : Nat) : Nat :=
  sorry

theorem solve_nice_integers_non_negative (a b : Nat) 
  (ha : a > 0) (hb : b > 0) (hbound_a : a ≤ 1000) (hbound_b : b ≤ 1000) :
  solve_nice_integers a b ≥ 0 := 
  sorry

theorem solve_nice_integers_base_case :
  solve_nice_integers 1 1 = 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_nice_integers 1 1

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_nice_integers 2 2

/-
info: 247750000
-/
-- #guard_msgs in
-- #eval solve_nice_integers 1000 1000

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible