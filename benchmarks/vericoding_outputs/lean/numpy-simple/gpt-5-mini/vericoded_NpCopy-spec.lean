import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem LLM_helper_true : True := trivial
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
  · exact arr.2
  · intro i; rfl
-- </vc-theorems>
