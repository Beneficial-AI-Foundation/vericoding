-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (s : String) : Option Float := sorry

theorem invalid_input_returns_none {s : String} 
  (h : s.isEmpty ∨ ¬∀ c ∈ s.data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '-', '*', '/', ' ']) :
  calculate s = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_expr_returns_some {expr : String} 
  (h : ∃ n : Float, calculate expr = some n) :
  ∃ n : Float, calculate expr = some n := sorry

theorem addition_commutative {a b : Nat} :
  calculate s!"{a}+{b}" = calculate s!"{b}+{a}" := sorry

theorem addition_associative {a b c : Nat} :
  ∀ n1 n2 : Float,
  calculate s!"({a}+{b})+{c}" = some n1 →
  calculate s!"{a}+({b}+{c})" = some n2 →
  Float.abs (n1 - n2) < 0.0001 := sorry

theorem division_by_nonzero {a : Nat} {b : Nat} (h : b > 0) :
  ∃ n : Float, calculate s!"{a}/{b}" = some n := sorry

theorem division_by_zero {a : Nat} :
  calculate s!"{a}/0" = none := sorry

theorem whitespace_invariant {expr : String} 
  (h : ∀ c ∈ expr.data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '-', '*', '/', ' ']) :
  calculate (expr.replace " " "") = calculate expr := sorry

theorem multiplication_by_one {x : Nat} :
  calculate s!"{x}*1" = some (x.toFloat) := sorry
-- </vc-theorems>