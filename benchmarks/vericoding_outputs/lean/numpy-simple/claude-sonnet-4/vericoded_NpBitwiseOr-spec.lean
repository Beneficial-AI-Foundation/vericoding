import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def bitwiseOr {n : Nat} (a b : Vector Nat n) : Vector Nat n :=
Vector.zipWith (· ||| ·) a b
-- </vc-definitions>

-- <vc-theorems>
theorem bitwiseOr_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseOr a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseOr a b)[i] = a[i] ||| b[i] :=
by
  constructor
  · simp [bitwiseOr]
  · intro i
    simp [bitwiseOr]
-- </vc-theorems>
