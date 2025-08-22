/-
# NumPy Equal Specification

Port of np_equal.dfy to Lean 4
-/

namespace DafnySpecs.NpEqual

/- LLM HELPER -/
lemma zipWith_length {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) :
  (List.zipWith f l1 l2).length = min l1.length l2.length := by
  induction l1 generalizing l2 with
  | nil => simp [List.zipWith]
  | cons h t ih =>
    cases l2 with
    | nil => simp [List.zipWith]
    | cons h' t' => simp [List.zipWith, ih]

/-- Element-wise equality comparison of two vectors -/
def equal {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.mk (Array.mk (List.zipWith (fun x y => x == y) a.toList b.toList))
    (by simp [zipWith_length, Vector.length_toList])

/-- Specification: The result has the same length as inputs -/
theorem equal_length {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n := by
  simp [equal, zipWith_length, Vector.length_toList]

/- LLM HELPER -/
lemma zipWith_get {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) 
  (i : Fin (min l1.length l2.length)) :
  (List.zipWith f l1 l2)[i] = f (l1[i.cast (Nat.min_le_left _ _)]) (l2[i.cast (Nat.min_le_right _ _)]) := by
  induction l1 generalizing l2 i with
  | nil => simp at i
  | cons h1 t1 ih =>
    cases l2 with
    | nil => simp at i
    | cons h2 t2 =>
      simp [List.zipWith]
      cases i using Fin.cases with
      | zero => simp
      | succ j => 
        simp [List.get_cons_succ]
        rw [ih]
        congr

/-- Specification: Each element is true iff corresponding input elements are equal -/
theorem equal_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (equal a b)[i] = (a[i] == b[i]) := by
  intro i
  simp [equal]
  have h1 : a.toList.length = n := a.2
  have h2 : b.toList.length = n := b.2
  have h3 : min a.toList.length b.toList.length = n := by simp [h1, h2]
  rw [Vector.get_mk]
  rw [Array.get_mk]
  rw [zipWith_get]
  simp [Vector.get_eq_get_toList]
  congr 1
  · simp [Fin.cast, h1]
  · simp [Fin.cast, h2]

end DafnySpecs.NpEqual