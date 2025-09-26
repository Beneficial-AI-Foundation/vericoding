import Mathlib
-- <vc-preamble>
def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def floorDivide {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n :=
Vector.zipWith (· / ·) a b.val
-- </vc-definitions>

-- <vc-theorems>
theorem floorDivide_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (floorDivide a b).toList.length = n ∧
  ∀ i : Fin n, (floorDivide a b)[i] = a[i] / (b.val[i]) :=
by
  constructor
  · simp [floorDivide]
  · intro i; simp [floorDivide, Vector.getElem_zipWith]
-- </vc-theorems>
