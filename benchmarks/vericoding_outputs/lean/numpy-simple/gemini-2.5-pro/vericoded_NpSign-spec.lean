import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def sign {n : Nat} (a : Vector Int n) : Vector Int n :=
a.map Int.sign
-- </vc-definitions>

-- <vc-theorems>
theorem sign_spec {n : Nat} (a : Vector Int n) :
  (sign a).toList.length = n ∧
  ∀ i : Fin n,
    (a[i] > 0 → (sign a)[i] = 1) ∧
    (a[i] = 0 → (sign a)[i] = 0) ∧
    (a[i] < 0 → (sign a)[i] = -1) :=
by
  constructor
  · simp [sign]
  · intro i
    simp [sign]
-- </vc-theorems>
