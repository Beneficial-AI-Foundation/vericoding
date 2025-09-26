import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def equal {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn (fun i => decide (a[i] = b[i]))
-- </vc-definitions>

-- <vc-theorems>
theorem equal_spec {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n ∧
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) :=
by
  constructor
  · simp [equal]
  · intro i
    apply propext
    simpa [equal] using (decide_eq_true_iff (p := a[i] = b[i]))
-- </vc-theorems>
