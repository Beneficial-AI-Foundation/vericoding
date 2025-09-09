-- <vc-helpers>
-- </vc-helpers>

def solve_xor_expression (a b : Nat) : Nat :=
  sorry

theorem xor_property (a b : Nat) :
  solve_xor_expression a b = a.xor b := by
  sorry

theorem xor_identity (x : Nat) : 
  solve_xor_expression x x = 0 := by
  sorry

theorem xor_commutative (a b : Nat) :
  solve_xor_expression a b = solve_xor_expression b a := by
  sorry

theorem xor_associative (a b c : Nat) :
  solve_xor_expression (solve_xor_expression a b) c = solve_xor_expression a (solve_xor_expression b c) := by
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_xor_expression 6 12

/-
info: 13
-/
-- #guard_msgs in
-- #eval solve_xor_expression 4 9

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_xor_expression 1 1

-- Apps difficulty: interview
-- Assurance level: guarded