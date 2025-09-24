-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def poly_from_roots (roots : List float) : List float := sorry

def evaluatePolynomial (coeffs : List float) (x : float) : float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem poly_from_roots_length {roots : List float} 
  (h : ∀ x ∈ roots, x.value ≥ -10 ∧ x.value ≤ 10) :
  (poly_from_roots roots).length = roots.length + 1 := sorry

theorem poly_from_roots_last_coeff {roots : List float}
  (h : ∀ x ∈ roots, x.value ≥ -10 ∧ x.value ≤ 10) :
  let result := poly_from_roots roots
  (result.getLast (sorry)).value = float.one.value := sorry

theorem poly_evaluates_to_zero {roots : List float} (root : float)
  (h1 : ∀ x ∈ roots, x.value ≥ -10 ∧ x.value ≤ 10)
  (h2 : root ∈ roots) :
  let result := poly_from_roots roots
  evaluatePolynomial result root = float.zero := sorry

theorem empty_roots :
  poly_from_roots [] = [float.one] := sorry

theorem zero_roots {n : Nat} (h : n > 0 ∧ n ≤ 10) :
  poly_from_roots (List.replicate n float.zero) = List.replicate n float.zero ++ [float.one] := sorry

/-
info: [-4, 1]
-/
-- #guard_msgs in
-- #eval poly_from_roots [4]

/-
info: [0, 0, 0, 0, 1]
-/
-- #guard_msgs in
-- #eval poly_from_roots [0, 0, 0, 0]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval poly_from_roots []
-- </vc-theorems>