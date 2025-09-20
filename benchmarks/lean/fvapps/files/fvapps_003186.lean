-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>