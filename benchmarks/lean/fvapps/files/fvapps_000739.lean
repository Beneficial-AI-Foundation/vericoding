-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_fx (b c : Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_fx_is_finite (b c : Float) :
  let result := find_min_fx b c
  Float.isFinite result := by sorry

theorem find_min_fx_is_minimum (b c : Float) :
  let result := find_min_fx b c
  let fx := fun (x : Float) => (x^2 + b*x + c)/Float.sin x
  ∀ x, 0 < x ∧ x < 3.14159 → result ≤ fx x + 0.000001 := by sorry 

theorem find_min_fx_positive_inputs (b c : Float) :
  0.1 ≤ b ∧ b ≤ 10 →
  0.1 ≤ c ∧ c ≤ 10 →
  0 < find_min_fx b c := by sorry

theorem find_min_fx_known_value :
  Float.abs (find_min_fx 2 2 - 5.8831725615) < 0.000001 := by sorry
-- </vc-theorems>