import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma vector_toList_length {α} {n} (v : Vector α n) : v.toList.length = n := by
  cases v with
  | mk l hl =>
    simpa [Vector.toList, hl]

-- </vc-helpers>

-- <vc-definitions>
def less {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn (fun i => decide (a[i] < b[i]))
-- </vc-definitions>

-- <vc-theorems>
theorem less_spec {n : Nat} (a b : Vector Int n) :
  (less a b).toList.length = n ∧
  ∀ i : Fin n, (less a b)[i] = (a[i] < b[i]) :=
by
  constructor
  · simpa using (vector_toList_length (less a b))
  · intro i
    by_cases h : a[i] < b[i]
    · simpa [less, Vector.get_ofFn, h]
    · simpa [less, Vector.get_ofFn, h]

-- </vc-theorems>
