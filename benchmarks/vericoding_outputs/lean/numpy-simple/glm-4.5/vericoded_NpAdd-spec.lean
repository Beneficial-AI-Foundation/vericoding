import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed as Vector.ofFn is sufficient
-- </vc-helpers>

-- <vc-definitions>
def add {n : Nat} (a b : Vector Int n) : Vector Int n :=
Vector.ofFn fun i : Fin n => a[i] + b[i]
-- </vc-definitions>

-- <vc-theorems>
theorem add_spec {n : Nat} (a b : Vector Int n) :
  (add a b).toList.length = n ∧
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] :=
by
  constructor
  · simp [add]
  · intro i
    simp [add]
-- </vc-theorems>
