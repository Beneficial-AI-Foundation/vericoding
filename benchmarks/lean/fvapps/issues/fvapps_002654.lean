-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bmi (weight height : Float) : Category :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bmi_returns_valid_category {weight height : Float} 
  (h1 : weight ≥ 1) (h2 : weight ≤ 500) 
  (h3 : height ≥ 0.5) (h4 : height ≤ 3.0) :
  let result := bmi weight height
  result = Category.Underweight ∨ 
  result = Category.Normal ∨
  result = Category.Overweight ∨ 
  result = Category.Obese :=
  sorry

theorem bmi_categories_are_monotonic {weight height : Float}
  (h1 : weight ≥ 1) (h2 : weight ≤ 500)
  (h3 : height ≥ 0.5) (h4 : height ≤ 3.0) :
  let bmiValue := weight / (height * height)
  (bmiValue ≤ 18.5 → bmi weight height = Category.Underweight) ∧
  (18.5 < bmiValue ∧ bmiValue ≤ 25 → bmi weight height = Category.Normal) ∧
  (25 < bmiValue ∧ bmiValue ≤ 30 → bmi weight height = Category.Overweight) ∧
  (30 < bmiValue → bmi weight height = Category.Obese) :=
  sorry

theorem bmi_zero_height_undefined {weight : Float} :
  ¬∃(result : Category), bmi weight 0 = result :=
  sorry

/-
info: 'Underweight'
-/
-- #guard_msgs in
-- #eval bmi 50 1.8

/-
info: 'Normal'
-/
-- #guard_msgs in
-- #eval bmi 80 1.8

/-
info: 'Obese'
-/
-- #guard_msgs in
-- #eval bmi 110 1.8
-- </vc-theorems>