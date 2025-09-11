-- <vc-preamble>
def operator_insertor (n : Int) : Option Int := sorry

theorem operator_insertor_output_range (n : Int) : 
  match operator_insertor n with
  | none => True 
  | some result => 0 ≤ result ∧ result ≤ 8
  := sorry

def expr_evaluates_to : Int → String → Prop := sorry

/- Helper function to check if expression uses given operators -/
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def expr_uses_ops : List String → String → Prop := sorry

theorem operator_insertor_result_exists (n : Int) (result : Int) :
  operator_insertor n = some result →
  ∃ ops : List String, 
    (ops.length = result) ∧
    (∀ op ∈ ops, op = "+" ∨ op = "-" ∨ op = "") ∧
    (∃ expr : String, expr_evaluates_to n expr ∧ expr_uses_ops ops expr)
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem operator_insertor_impossible_large (n : Int) :
  n ≥ 10^10 → operator_insertor n = none := sorry

theorem operator_insertor_impossible_small (n : Int) :
  n ≤ -(10^10) → operator_insertor n = none := sorry

/- Helper function to check if a string expression evaluates to a number -/

/-
info: 5
-/
-- #guard_msgs in
-- #eval operator_insertor 11

/-
info: 3
-/
-- #guard_msgs in
-- #eval operator_insertor 100

/-
info: None
-/
-- #guard_msgs in
-- #eval operator_insertor 160
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded