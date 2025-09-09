def value (a b : Nat) (op : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def solve_expression (expr : String) : Nat :=
  sorry

theorem value_commutativity {a b : Nat} {op : String} (h : op = "&" ∨ op = "|") :
  value a b op = value b a op := by
  sorry

theorem value_nonnegativity {a b : Nat} {op : String} (h : op = "&" ∨ op = "|" ∨ op = "^") :
  value a b op ≥ 0 := by
  sorry

theorem solve_expr_type {expr : String} : 
  ∃ (n : Nat), solve_expression expr = n := by
  sorry

theorem solve_expr_nonneg {expr : String} :
  solve_expression expr ≥ 0 := by
  sorry

/-
info: 43
-/
-- #guard_msgs in
-- #eval solve_expression "3^40|10^2"

/-
info: 95
-/
-- #guard_msgs in
-- #eval solve_expression "92^95|56&2&3"

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_expression "1&2|3"

-- Apps difficulty: interview
-- Assurance level: guarded