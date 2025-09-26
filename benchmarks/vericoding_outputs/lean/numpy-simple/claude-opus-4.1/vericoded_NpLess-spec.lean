import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma vector_toList_length {n : Nat} {α : Type*} (v : Vector α n) :
  v.toList.length = n := by
  cases v with
  | mk arr h =>
    simp [Vector.toList]
    exact h

-- LLM HELPER
lemma vector_zipWith_toList {n : Nat} {α β γ : Type*} (f : α → β → γ) (a : Vector α n) (b : Vector β n) :
  (Vector.zipWith f a b).toList = List.zipWith f a.toList b.toList := by
  cases a; cases b
  simp [Vector.zipWith, Vector.toList]

-- LLM HELPER  
lemma vector_zipWith_get {n : Nat} {α β γ : Type*} (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Fin n) :
  (Vector.zipWith f a b)[i] = f a[i] b[i] := by
  cases ha : a; cases hb : b
  simp [Vector.zipWith]
-- </vc-helpers>

-- <vc-definitions>
def less {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.zipWith (fun x y => decide (x < y)) a b
-- </vc-definitions>

-- <vc-theorems>
theorem less_spec {n : Nat} (a b : Vector Int n) :
  (less a b).toList.length = n ∧
  ∀ i : Fin n, (less a b)[i] = (a[i] < b[i]) :=
by
  simp only [less]
  constructor
  · apply vector_toList_length
  · intro i
    simp only [vector_zipWith_get]
    simp only [decide_eq_true_iff]
-- </vc-theorems>
