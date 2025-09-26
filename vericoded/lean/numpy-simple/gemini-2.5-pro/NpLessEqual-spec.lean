import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers are needed for this implementation.
-- </vc-helpers>

-- <vc-definitions>
def lessEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.zipWith (fun x y => decide (x ≤ y)) a b
-- </vc-definitions>

-- <vc-theorems>
theorem lessEqual_spec {n : Nat} (a b : Vector Int n) :
  (lessEqual a b).toList.length = n ∧
  ∀ i : Fin n, (lessEqual a b)[i] = (a[i] ≤ b[i]) :=
by
  constructor
  case left =>
    simp [lessEqual]
  case right =>
    intro i
    simp [lessEqual]
-- </vc-theorems>
