import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Indexing property for zipWith
lemma Vector.zipWith_get {α β γ : Type*} {n : Nat} (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Fin n) :
  (Vector.zipWith f a b)[i] = f a[i] b[i] := by
  simp [Vector.zipWith, List.getElem_zipWith]
-- </vc-helpers>

-- <vc-definitions>
def greaterEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.zipWith (· ≥ ·) a b
-- </vc-definitions>

-- <vc-theorems>
theorem greaterEqual_spec {n : Nat} (a b : Vector Int n) :
  (greaterEqual a b).toList.length = n ∧
  ∀ i : Fin n, (greaterEqual a b)[i] = (a[i] ≥ b[i]) :=
⟨by simp [greaterEqual, Vector.zipWith], fun i => by simp [greaterEqual, Vector.zipWith_get]⟩
-- </vc-theorems>
