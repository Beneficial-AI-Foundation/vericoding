import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple copy operation
-- </vc-helpers>

-- <vc-definitions>
def copy {n : Nat} (arr : Vector Int n) : Vector Int n :=
arr
-- </vc-definitions>

-- <vc-theorems>
theorem copy_spec {n : Nat} (arr : Vector Int n) :
  (copy arr).toList.length = n ∧
  ∀ i : Fin n, (copy arr)[i] = arr[i] :=
⟨by simp [copy], fun i => by simp [copy]⟩
-- </vc-theorems>
