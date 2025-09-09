-- <vc-helpers>
-- </vc-helpers>

def celsius_to_romer (celsius : Float) : Float := sorry

theorem celsius_to_romer_zero_point :
  let romer := celsius_to_romer 0
  (romer - 7.5).abs < 0.0000000001 := by sorry

theorem celsius_to_romer_conversion_formula (celsius : Float) 
    (h1 : celsius ≥ -273.15) (h2 : celsius ≤ 1000) :
  let romer := celsius_to_romer celsius
  let expected := (celsius * 21 / 40) + 7.5
  (romer - expected).abs < 0.0000000001 := by sorry

-- Apps difficulty: introductory
-- Assurance level: guarded