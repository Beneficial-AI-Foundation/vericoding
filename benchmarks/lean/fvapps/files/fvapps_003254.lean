-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tax_calculator (x : Float) : Float := sorry

theorem tax_monotonic {x delta : Float} (h1 : x ≥ 0) (h2 : delta ≥ 0) (h3 : x ≤ 1000) (h4 : delta ≤ 100) :
  tax_calculator (x + delta) ≥ tax_calculator x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tax_invalid_inputs (x : Float) (h : x < 0) :
  tax_calculator x = 0 := sorry

theorem tax_first_bracket {x : Float} (h1 : 0 ≤ x) (h2 : x ≤ 10) :
  tax_calculator x = x/10 := sorry

theorem tax_second_bracket {x : Float} (h1 : 10 < x) (h2 : x ≤ 20) :
  tax_calculator x = 1 + (x-10) * 0.07 := sorry

theorem tax_third_bracket {x : Float} (h1 : 20 < x) (h2 : x ≤ 30) :
  tax_calculator x = 1.7 + (x-20) * 0.05 := sorry

theorem tax_fourth_bracket {x : Float} (h1 : 30 < x) (h2 : x ≤ 100) :
  tax_calculator x = 2.2 + (x-30) * 0.03 := sorry
-- </vc-theorems>