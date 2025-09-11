-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.variance (l : List Int) : Float := sorry

def regressionLine (x : List Int) (y : List Int) : Float × Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem regression_line_outputs_float_pair 
  (x y : List Int) 
  (h1 : x.length ≥ 3) 
  (h2 : y.length = x.length)
  (h3 : (List.variance x) > 0) :
  let (a, b) := regressionLine x y
  ∃ (a' b' : Float), a = a' ∧ b = b' := sorry

theorem regression_line_outputs_finite 
  (x y : List Int)
  (h1 : x.length ≥ 3)
  (h2 : y.length = x.length) 
  (h3 : (List.variance x) > 0) :
  let (a, b) := regressionLine x y
  ¬a.isNaN ∧ ¬b.isNaN := sorry

/-
info: (114.381, -1.4457)
-/
-- #guard_msgs in
-- #eval regressionLine [25, 30, 35, 40, 45, 50] [78, 70, 65, 58, 48, 42]

/-
info: (80.7777, 1.138)
-/
-- #guard_msgs in
-- #eval regressionLine [56, 42, 72, 36, 63, 47, 55, 49, 38, 42, 68, 60] [147, 125, 160, 118, 149, 128, 150, 145, 115, 140, 152, 155]

/-
info: (0.514, 0.0028)
-/
-- #guard_msgs in
-- #eval regressionLine [0, 10, 20, 30, 40] [0.51, 0.55, 0.57, 0.59, 0.63]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded