import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed
-- </vc-helpers>

-- <vc-definitions>
def greaterEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.zipWith (· ≥ ·) a b
-- </vc-definitions>

-- <vc-theorems>
theorem greaterEqual_spec {n : Nat} (a b : Vector Int n) :
  (greaterEqual a b).toList.length = n ∧
  ∀ i : Fin n, (greaterEqual a b)[i] = (a[i] ≥ b[i]) :=
by
  constructor
  · simp [greaterEqual]
  · intro i
    simp [greaterEqual]
-- </vc-theorems>
