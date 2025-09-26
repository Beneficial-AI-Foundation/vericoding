import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem vector_toList_length {α} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  cases v with
  | mk l hl => simpa [Vector.toList] using hl
-- </vc-helpers>

-- <vc-definitions>
def bitwiseOr {n : Nat} (a b : Vector Nat n) : Vector Nat n :=
Vector.ofFn (fun i => a[i] ||| b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem bitwiseOr_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseOr a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseOr a b)[i] = a[i] ||| b[i] :=
by
  constructor
  · simp
  · intro i
    simp [bitwiseOr]
-- </vc-theorems>
