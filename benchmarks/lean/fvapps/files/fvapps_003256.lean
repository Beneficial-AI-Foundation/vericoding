-- <vc-preamble>
def pi : Float := 3.14159
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def circle_area (radius : Float) : Option Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem circle_area_invalid_inputs {x : Float} (h : x ≤ 0) :
  circle_area x = none :=
sorry

theorem circle_area_positive_inputs {x : Float} (h : x > 0) :
  match circle_area x with
  | some result =>
    result > 0
  | none => False :=
sorry

theorem circle_area_zero :
  circle_area 0 = none :=
sorry
-- </vc-theorems>