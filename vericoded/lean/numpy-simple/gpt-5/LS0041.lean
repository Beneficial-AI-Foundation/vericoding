import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem vector_toList_length {α : Type _} {n : Nat} (v : Vector α n) :
  v.toList.length = n := by
  cases v with
  | mk l h => simpa using h
-- </vc-helpers>

-- <vc-definitions>
def power {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n :=
Vector.ofFn (fun i => (a[i]) ^ (b[i]))
-- </vc-definitions>

-- <vc-theorems>
theorem power_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (power a b).toList.length = n ∧
  ∀ i : Fin n, (power a b)[i] = (a[i]) ^ (b[i]) :=
by
  constructor
  · simpa using vector_toList_length (power a b)
  · intro i
    simp [power]
-- </vc-theorems>
