import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple copy implementation
-- </vc-helpers>

-- <vc-definitions>
def copy {n : Nat} (arr : Vector Int n) : Vector Int n :=
arr
-- </vc-definitions>

-- <vc-theorems>
theorem copy_spec {n : Nat} (arr : Vector Int n) :
  (copy arr).toList.length = n ∧
  ∀ i : Fin n, (copy arr)[i] = arr[i] :=
by
  constructor
  · -- Prove length equality
    simp [copy]
  · -- Prove element-wise equality
    intro i
    simp [copy]
-- </vc-theorems>
