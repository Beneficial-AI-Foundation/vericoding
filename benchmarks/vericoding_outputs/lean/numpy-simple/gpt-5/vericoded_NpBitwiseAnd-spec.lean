import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem vector_get_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simpa

-- LLM HELPER
@[simp] theorem vector_toList_length_ofFn {α : Type _} {n : Nat} (f : Fin n → α) :
  (Vector.ofFn f).toList.length = n := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def bitwiseAnd {n : Nat} (a b : Vector Nat n) : Vector Nat n :=
Vector.ofFn (fun i => a[i] &&& b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem bitwiseAnd_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseAnd a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseAnd a b)[i] = a[i] &&& b[i] :=
by
  constructor
  · simp [bitwiseAnd]
  · intro i; simp [bitwiseAnd]
-- </vc-theorems>
