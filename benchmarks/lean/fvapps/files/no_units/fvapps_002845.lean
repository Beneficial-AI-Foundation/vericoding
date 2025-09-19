-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def poly_add (p1 p2 : List Int) : List Int := sorry

theorem poly_add_length (p1 p2 : List Int) :
  (poly_add p1 p2).length = max p1.length p2.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem poly_add_empty_left (p : List Int) :
  poly_add [] p = p := sorry

theorem poly_add_empty_right (p : List Int) :
  poly_add p [] = p := sorry

theorem poly_add_comm (p1 p2 : List Int) :
  poly_add p1 p2 = poly_add p2 p1 := sorry

theorem poly_add_coeff (p1 p2 : List Int) (i : Nat) (h1 : i < p1.length) (h2 : i < p2.length) 
  (h3 : i < (poly_add p1 p2).length) :
  (poly_add p1 p2)[i] = p1[i] + p2[i] := sorry

theorem poly_add_zeros (p : List Int) :
  poly_add p (List.replicate p.length 0) = p := sorry
-- </vc-theorems>