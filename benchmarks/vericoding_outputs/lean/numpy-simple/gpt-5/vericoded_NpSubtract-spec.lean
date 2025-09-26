import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed for this file
-- </vc-helpers>

-- <vc-definitions>
def subtract {n : Nat} (a b : Vector Int n) : Vector Int n :=
Vector.ofFn (fun i => a[i] - b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem subtract_spec {n : Nat} (a b : Vector Int n) :
  (subtract a b).toList.length = n ∧
  ∀ i : Fin n, (subtract a b)[i] = a[i] - b[i] :=
by
  constructor
  · simpa using (Vector.toList_length (subtract a b))
  · intro i
    simpa [subtract] using (Vector.get_ofFn (f := fun j => a[j] - b[j]) i)
-- </vc-theorems>
