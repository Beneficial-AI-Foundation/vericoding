-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def evaluate_lisp (s : String) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arithmetic_evaluation (op : String) (x y : Int) 
  (h : op = "add" ∨ op = "mult") :
  evaluate_lisp s!"({op} {x} {y})" = 
    if op = "add" then x + y else x * y := by
  sorry

theorem let_evaluation (var : String) (val expr : Int) 
  (h : ∀ c ∈ var.data, c.isAlpha ∧ c.isLower) :
  evaluate_lisp s!"(let {var} {val} {expr})" = expr := by
  sorry

theorem add_commutative (x y : Int) :
  evaluate_lisp s!"(add {x} {y})" = evaluate_lisp s!"(add {y} {x})" := by
  sorry

theorem mult_commutative (x y : Int) :
  evaluate_lisp s!"(mult {x} {y})" = evaluate_lisp s!"(mult {y} {x})" := by
  sorry

theorem mult_identity (x : Int) :
  evaluate_lisp s!"(mult {x} 1)" = x ∧ 
  evaluate_lisp s!"(mult 1 {x})" = x := by
  sorry

theorem add_identity (x : Int) :
  evaluate_lisp s!"(add {x} 0)" = x ∧
  evaluate_lisp s!"(add 0 {x})" = x := by
  sorry
-- </vc-theorems>