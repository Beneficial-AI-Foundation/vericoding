-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rain_amount (mm : Int) : String := sorry

theorem rain_amount_preserves_invariants (mm : Int) :
  (mm < 40 → rain_amount mm = s!"You need to give your plant {40 - mm}mm of water") ∧
  (mm ≥ 40 → rain_amount mm = "Your plant has had more than enough water for today!") :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rain_amount_calculation (mm : Int) :
  (mm < 40 → rain_amount mm = s!"You need to give your plant {40 - mm}mm of water") ∧
  (mm ≥ 40 → rain_amount mm = "Your plant has had more than enough water for today!") :=
sorry
-- </vc-theorems>