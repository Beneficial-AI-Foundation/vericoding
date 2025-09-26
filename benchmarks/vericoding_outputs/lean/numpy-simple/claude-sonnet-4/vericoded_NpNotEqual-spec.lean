import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Use Vector.ofFn for functional construction
-- This creates a Vector from a function Fin n → α
-- </vc-helpers>

-- <vc-definitions>
def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn (fun i => a[i] ≠ b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) :=
⟨by simp [notEqual, Vector.toList_ofFn], fun i => by simp [notEqual, Vector.get_ofFn]⟩
-- </vc-theorems>
