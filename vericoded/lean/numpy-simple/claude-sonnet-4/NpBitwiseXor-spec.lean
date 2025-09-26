import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Vector XOR utilities
-- Helper to construct vector from function
def vectorFromFn {α : Type*} {n : Nat} (f : Fin n → α) : Vector α n :=
  Vector.ofFn f

-- Helper lemma for ofFn length
lemma vector_ofFn_length {α : Type*} {n : Nat} (f : Fin n → α) :
  (Vector.ofFn f).toList.length = n :=
by simp [Vector.ofFn]

-- Helper lemma for ofFn indexing
lemma vector_ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i :=
by simp [Vector.ofFn]
-- </vc-helpers>

-- <vc-definitions>
def bitwiseXor {n : Nat} (a b : Vector Nat n) : Vector Nat n :=
Vector.ofFn (fun i => a[i] ^^^ b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem bitwiseXor_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseXor a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseXor a b)[i] = a[i] ^^^ b[i] :=
⟨by
    unfold bitwiseXor
    simp [vector_ofFn_length],
  fun i => by
    unfold bitwiseXor
    simp [vector_ofFn_get]⟩
-- </vc-theorems>
