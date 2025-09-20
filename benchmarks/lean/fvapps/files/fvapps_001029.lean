-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def value (a b : Nat) (op : String) : Nat :=
  sorry

def solve_expression (expr : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>