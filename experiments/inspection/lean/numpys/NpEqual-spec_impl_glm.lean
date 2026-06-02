import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma Vector.ofFn_length {n : Nat} {α : Type} (f : Fin n → α) :
    (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn]

-- LLM HELPER
lemma Vector.ofFn_get {n : Nat} {α : Type} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn]
-- </vc-helpers>

-- <vc-definitions>
def equal {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn fun i : Fin n => a[i] = b[i]
-- </vc-definitions>

-- <vc-theorems>
theorem equal_spec {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n ∧
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) :=
by
  constructor
  · simp [equal]
  · intro i
    simp [equal]
-- </vc-theorems>
