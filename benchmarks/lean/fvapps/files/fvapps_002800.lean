-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fold_to (distance : Float) (thickness : Float := 0.0001) : Option Float := sorry

theorem fold_to_positive_distance {distance : Float} 
  (h1 : distance ≥ 0) 
  (h2 : distance < 1e10) :
  let res := fold_to distance 
  match res with
  | some n => n ≥ 0 ∧ 2^n * 0.0001 ≥ distance
  | none => False := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fold_to_negative_distance {distance : Float}
  (h : distance < 0) :
  fold_to distance = none := sorry

theorem fold_to_custom_thickness {distance thickness : Float}
  (h1 : distance ≥ 0)
  (h2 : distance < 1e10)
  (h3 : thickness ≥ 1e-10)
  (h4 : thickness ≤ 1.0) :
  let res := fold_to distance thickness
  match res with
  | some n => n ≥ 0 ∧ 2^n * thickness ≥ distance
  | none => True := sorry

theorem fold_to_zero :
  fold_to 0 = some 0 := sorry

theorem fold_to_zero_custom_thickness :
  fold_to 0 0.1 = some 0 := sorry
-- </vc-theorems>