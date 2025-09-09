-- <vc-helpers>
-- </vc-helpers>

def combat (health damage : Int) : Int := sorry

theorem combat_positive_inputs (health damage : Int) 
  (h₁ : health ≥ 0) (h₂ : damage ≥ 0) : 
  combat health damage = max 0 (health - damage) ∧ 
  combat health damage ≥ 0 := 
  sorry

/-
info: 95
-/
-- #guard_msgs in
-- #eval combat 100 5

/-
info: 67
-/
-- #guard_msgs in
-- #eval combat 83 16

/-
info: 0
-/
-- #guard_msgs in
-- #eval combat 20 30

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible