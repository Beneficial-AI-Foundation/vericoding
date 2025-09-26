import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn (fun i => decide (a[i] ≠ b[i]))
-- </vc-definitions>

-- <vc-theorems>
theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) :=
by
  constructor
  · simp [notEqual, Vector.toList_ofFn]
  · intro i
    simp [notEqual]
-- </vc-theorems>
