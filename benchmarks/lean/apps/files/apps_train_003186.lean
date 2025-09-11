-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def poly_subtract : List Int → List Int → List Int
  | p1, p2 => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem poly_subtract_length (p1 p2 : List Int) :
  p1.length > 0 ∨ p2.length > 0 →
  (poly_subtract p1 p2).length ≤ max p1.length p2.length := sorry

theorem poly_subtract_self (p : List Int) :
  ∀ x ∈ poly_subtract p p, x = 0 := sorry

theorem poly_subtract_empty (p : List Int) :
  poly_subtract p [] = p := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval poly_subtract [] []

/-
info: [1, 2, 3, 4, 5, 6]
-/
-- #guard_msgs in
-- #eval poly_subtract [1, 2, 3, 4, 5, 6] []

/-
info: [-1, -2, -3, -4, -5, -6]
-/
-- #guard_msgs in
-- #eval poly_subtract [] [1, 2, 3, 4, 5, 6]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible