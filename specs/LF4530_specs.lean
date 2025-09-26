-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sat (f : Formula) : Option Model := sorry

theorem sat_returns_model_or_false (f : Formula) (m : Model) :
  (sat f = some m) → ∀ s ∈ m, ∃ name, Formula.lit name = Formula.lit s
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem not_p_and_p_unsatisfiable (p : Formula) :
  sat (Formula.and [p, Formula.not p]) = none 
  := sorry

theorem p_or_not_p_satisfiable (p : Formula) :
  sat (Formula.or [p, Formula.not p]) ≠ none
  := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval sat Formula()
-- </vc-theorems>