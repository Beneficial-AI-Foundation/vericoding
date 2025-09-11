-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def converter (mpg : Float) : Float := sorry 

namespace converter
-- </vc-definitions>

-- <vc-theorems>
theorem converter_positive {mpg : Float} (h : mpg ≥ 1) : converter mpg > 0 := sorry 

theorem converter_proportional {mpg : Float} (h1 : mpg ≥ 1) (h2 : mpg ≤ 500) : 
  0.30 * mpg ≤ converter mpg ∧ converter mpg ≤ 0.40 * mpg := sorry

end converter

/-
info: 3.54
-/
-- #guard_msgs in
-- #eval converter 10

/-
info: 8.5
-/
-- #guard_msgs in
-- #eval converter 24

/-
info: 12.74
-/
-- #guard_msgs in
-- #eval converter 36
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded