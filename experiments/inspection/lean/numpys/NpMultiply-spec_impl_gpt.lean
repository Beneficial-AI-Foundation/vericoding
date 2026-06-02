import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers required for this file.
-- </vc-helpers>

-- <vc-definitions>
def multiply {n : Nat} (a b : Vector Int n) : Vector Int n :=
Vector.ofFn (fun i => a[i] * b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_spec {n : Nat} (a b : Vector Int n) :
  (multiply a b).toList.length = n ∧
  ∀ i : Fin n, (multiply a b)[i] = a[i] * b[i] :=
by
  constructor
  · simpa [multiply]
  · intro i
    simpa [multiply]
-- </vc-theorems>
