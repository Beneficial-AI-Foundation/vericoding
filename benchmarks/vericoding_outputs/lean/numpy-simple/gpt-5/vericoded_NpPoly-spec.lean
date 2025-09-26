import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no additional helpers needed
-- </vc-helpers>

-- <vc-definitions>
def poly_helper {n : Nat} (roots : Vector Float n) (val : Nat) : Vector Float n :=
Vector.ofFn (fun (_ : Fin n) => 1.0)

def poly {n : Nat} (roots : Vector Float n) : Vector Float n :=
poly_helper roots (n - 1)
-- </vc-definitions>

-- <vc-theorems>
theorem poly_spec {n : Nat} (roots : Vector Float n)
  (h : n > 0) :
  let coeff := poly roots
  (coeff.toList.length = n) ∧
  (∀ i : Fin n, coeff[i] = (poly_helper roots (n - 1))[i]) :=
by
  intro coeff
  constructor
  · simpa [coeff] using (poly roots).property
  · intro i; simp [coeff, poly, poly_helper]

theorem poly_helper_spec {n : Nat} (roots : Vector Float n) (val : Nat)
  (h1 : n > 0)
  (h2 : val > 0) :
  let coeff := poly_helper roots val
  (coeff.toList.length = n) ∧
  (coeff[0]! = 1.0) :=
by
  intro coeff
  constructor
  · simpa [coeff] using (poly_helper roots val).property
  · have hn : 0 < n := h1
    simpa [coeff, poly_helper, hn]
-- </vc-theorems>
