namespace NpPoly

def poly_helper {n : Nat} (roots : Vector Float n) (val : Nat) : Vector Float n := sorry

def poly {n : Nat} (roots : Vector Float n) : Vector Float n := sorry

theorem poly_spec {n : Nat} (roots : Vector Float n)
  (h : n > 0) :
  let coeff := poly roots
  (coeff.toList.length = n) ∧
  (∀ i : Fin n, coeff[i] = (poly_helper roots (n - 1))[i]) := sorry

theorem poly_helper_spec {n : Nat} (roots : Vector Float n) (val : Nat)
  (h1 : n > 0)
  (h2 : val > 0) :
  let coeff := poly_helper roots val
  (coeff.toList.length = n) ∧
  (coeff[0]! = 1.0) := sorry

end NpPoly
