-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def poly_multiply (p1 p2 : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem poly_multiply_length (p1 p2 : List Int) :
  (p1 = [] ∨ p2 = []) → poly_multiply p1 p2 = [] ∧
  (p1 ≠ [] ∧ p2 ≠ []) → List.length (poly_multiply p1 p2) = List.length p1 + List.length p2 - 1 :=
  sorry

theorem poly_multiply_zero (poly : List Int) (h : poly ≠ []) :
  poly_multiply poly [0] = List.replicate (List.length poly) 0 ∧
  poly_multiply [0] poly = List.replicate (List.length poly) 0 :=
  sorry

theorem poly_multiply_one (poly : List Int) (h : poly ≠ []) :
  poly_multiply poly [1] = poly ∧
  poly_multiply [1] poly = poly :=
  sorry

theorem poly_multiply_commutative (p1 p2 : List Int) :
  poly_multiply p1 p2 = poly_multiply p2 p1 :=
  sorry

theorem poly_multiply_empty (poly : List Int) :
  poly_multiply poly [] = [] ∧
  poly_multiply [] poly = [] :=
  sorry
-- </vc-theorems>