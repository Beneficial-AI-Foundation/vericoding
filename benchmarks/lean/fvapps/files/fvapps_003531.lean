-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def starting_mark (height : Float) : Float := sorry

theorem starting_mark_in_range (height : Float)
  (h1 : 1.52 ≤ height) (h2 : height ≤ 1.83) :
  9.45 ≤ starting_mark height ∧ starting_mark height ≤ 10.67 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem starting_mark_linear (height : Float)
  (h1 : 1.52 ≤ height) (h2 : height ≤ 1.83) :
  let slope := (10.67 - 9.45) / (1.83 - 1.52)
  let expected := 9.45 + slope * (height - 1.52)
  (starting_mark height - expected).abs < 0.001 := sorry

theorem starting_mark_rounding (height : Float) :
  let mark := starting_mark height
  let decimal := mark - mark.floor
  decimal < 0.01 := sorry

theorem starting_mark_edge_cases :
  starting_mark 1.52 = 9.45 ∧
  starting_mark 1.83 = 10.67 := sorry
-- </vc-theorems>