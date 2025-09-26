import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def greater {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn (fun i => a[i] > b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem greater_spec {n : Nat} (a b : Vector Int n) :
  (greater a b).toList.length = n ∧
  ∀ i : Fin n, (greater a b)[i] = (a[i] > b[i]) :=
⟨by simp [greater, Vector.toList_ofFn], fun i => by simp [greater, Vector.getElem_ofFn]⟩
-- </vc-theorems>
