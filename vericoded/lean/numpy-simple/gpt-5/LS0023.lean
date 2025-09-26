import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers needed
-- </vc-helpers>

-- <vc-definitions>
def greaterEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn (fun i => a[i] ≥ b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem greaterEqual_spec {n : Nat} (a b : Vector Int n) :
  (greaterEqual a b).toList.length = n ∧
  ∀ i : Fin n, (greaterEqual a b)[i] = (a[i] ≥ b[i]) :=
by
  constructor
  · simpa [greaterEqual]
  · intro i
    simpa [greaterEqual]
-- </vc-theorems>
