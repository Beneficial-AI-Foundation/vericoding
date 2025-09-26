import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma Vector.toList_length {α : Type*} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  cases v
  simp [Vector.toList]
  assumption
-- </vc-helpers>

-- <vc-definitions>
def equal {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn fun i => decide (a[i] = b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem equal_spec {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n ∧
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) :=
by
  constructor
  · -- First part: length is n
    simp [equal, Vector.toList_ofFn, List.length_ofFn]
  · -- Second part: indexing property
    intro i
    simp [equal, Vector.getElem_ofFn]
-- </vc-theorems>
