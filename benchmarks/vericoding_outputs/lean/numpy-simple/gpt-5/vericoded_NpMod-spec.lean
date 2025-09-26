import Mathlib
-- <vc-preamble>
def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem Vector.length_of_toList {α} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  simpa using v.toList_length

-- LLM HELPER
@[simp] theorem Vector.get_ofFn' {α} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simpa using Vector.get_ofFn f i

-- </vc-helpers>

-- <vc-definitions>
def mod {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n :=
Vector.ofFn (fun i => a[i] % b.val[i])
-- </vc-definitions>

-- <vc-theorems>
theorem mod_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (mod a b).toList.length = n ∧
  ∀ i : Fin n, (mod a b)[i] = a[i] % (b.val[i]) :=
by
  constructor
  · simpa using (Vector.length_of_toList (mod a b))
  · intro i
    simp [mod]

-- </vc-theorems>
