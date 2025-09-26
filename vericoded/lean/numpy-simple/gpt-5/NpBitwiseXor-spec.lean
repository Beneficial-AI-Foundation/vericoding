import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem vector_toList_length {α} {n : Nat} (v : Vector α n) :
  v.toList.length = n := by
  simpa using Vector.toList_length v

-- LLM HELPER
@[simp] theorem vector_zipWith_get_xor {n : Nat} (a b : Vector Nat n) (i : Fin n) :
  (Vector.zipWith (fun x y : Nat => x ^^^ y) a b)[i] = a[i] ^^^ b[i] := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def bitwiseXor {n : Nat} (a b : Vector Nat n) : Vector Nat n :=
Vector.zipWith (fun x y => x ^^^ y) a b
-- </vc-definitions>

-- <vc-theorems>
theorem bitwiseXor_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseXor a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseXor a b)[i] = a[i] ^^^ b[i] :=
by
  constructor
  · simpa using (Vector.toList_length (bitwiseXor a b))
  · intro i
    simp [bitwiseXor]
-- </vc-theorems>
