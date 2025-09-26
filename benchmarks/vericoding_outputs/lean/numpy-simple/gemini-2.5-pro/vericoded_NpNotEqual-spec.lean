import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.zipWith (fun x y => x != y) a b
-- </vc-definitions>

-- <vc-theorems>
theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) :=
by
  constructor
  · simp [notEqual]
  · intro i
    simp [notEqual, decide_eq_false_iff_not]
-- </vc-theorems>
