-- <vc-helpers>
-- </vc-helpers>

def rain_amount (mm : Int) : String := sorry

theorem rain_amount_preserves_invariants (mm : Int) :
  (mm < 40 → rain_amount mm = s!"You need to give your plant {40 - mm}mm of water") ∧
  (mm ≥ 40 → rain_amount mm = "Your plant has had more than enough water for today!") :=
sorry

theorem rain_amount_calculation (mm : Int) :
  (mm < 40 → rain_amount mm = s!"You need to give your plant {40 - mm}mm of water") ∧
  (mm ≥ 40 → rain_amount mm = "Your plant has had more than enough water for today!") :=
sorry

/-
info: 'Your plant has had more than enough water for today!'
-/
-- #guard_msgs in
-- #eval rain_amount 100

/-
info: 'Your plant has had more than enough water for today!'
-/
-- #guard_msgs in
-- #eval rain_amount 40

/-
info: 'You need to give your plant 35mm of water'
-/
-- #guard_msgs in
-- #eval rain_amount 5

-- Apps difficulty: introductory
-- Assurance level: unguarded