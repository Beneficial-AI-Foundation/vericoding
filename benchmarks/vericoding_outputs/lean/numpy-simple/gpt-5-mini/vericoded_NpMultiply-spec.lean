import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Helper: indexing of Vector.ofFn reduces to the generating function -/
theorem Vector_ofFn_get {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  dsimp [Vector.ofFn]
  simp

-- LLM HELPER
/-- Helper: length of Vector.ofFn.toList is n -/
theorem Vector_ofFn_toList_length {α : Type} {n : Nat} (f : Fin n → α) : (Vector.ofFn f).toList.length = n := by
  dsimp [Vector.ofFn]
  simp
-- </vc-helpers>

-- <vc-definitions>
def multiply {n : Nat} (a b : Vector Int n) : Vector Int n :=
Vector.ofFn fun i => a[i] * b[i]
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_spec {n : Nat} (a b : Vector Int n) :
  (multiply a b).toList.length = n ∧
  ∀ i : Fin n, (multiply a b)[i] = a[i] * b[i] :=
by
  dsimp [multiply]
  constructor
  · apply Vector_ofFn_toList_length
  · intro i
    apply Vector_ofFn_get
-- </vc-theorems>
