import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for basic implementation
-- </vc-helpers>

-- <vc-definitions>
def subtract {n : Nat} (a b : Vector Int n) : Vector Int n :=
Vector.zipWith (· - ·) a b
-- </vc-definitions>

-- <vc-theorems>
theorem subtract_spec {n : Nat} (a b : Vector Int n) :
  (subtract a b).toList.length = n ∧
  ∀ i : Fin n, (subtract a b)[i] = a[i] - b[i] :=
by
  constructor
  · simp [subtract]
  · intro i
    simp [subtract]
-- </vc-theorems>
