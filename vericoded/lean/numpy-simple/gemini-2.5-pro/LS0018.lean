import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def equal {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn fun i => a[i] == b[i]
-- </vc-definitions>

-- <vc-theorems>
theorem equal_spec {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n ∧
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) :=
by
  constructor
  · simp
  · intro i
    simp [equal, beq_iff_eq]
-- </vc-theorems>
