/-
# NumPy Multiply Specification

Port of np_multiply.dfy to Lean 4
-/

namespace DafnySpecs.NpMultiply

/-- Element-wise multiplication of two vectors -/
def multiply {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.mk (List.zipWith (· * ·) a.toList b.toList) (by simp [List.zipWith_length, Vector.toList_length])

/- LLM HELPER -/
lemma zipWith_length {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) :
  (List.zipWith f l1 l2).length = min l1.length l2.length := by
  induction l1 generalizing l2 with
  | nil => simp [List.zipWith]
  | cons a as ih =>
    cases l2 with
    | nil => simp [List.zipWith]
    | cons b bs => simp [List.zipWith, ih]

/- LLM HELPER -/
lemma zipWith_get {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) 
  (i : Fin (min l1.length l2.length)) :
  (List.zipWith f l1 l2)[i] = f (l1[i.cast (Nat.min_le_left _ _)]) (l2[i.cast (Nat.min_le_right _ _)]) := by
  induction l1 generalizing l2 i with
  | nil => 
    simp at i
  | cons a as ih =>
    cases l2 with
    | nil => simp at i
    | cons b bs =>
      simp [List.zipWith]
      cases i using Fin.cases with
      | zero => simp
      | succ j => 
        simp [List.get_cons_succ]
        have : j.val < min as.length bs.length := by
          have : j.val + 1 < min (as.length + 1) (bs.length + 1) := i.isLt
          simp at this
          exact Nat.lt_min.mpr ⟨Nat.lt_of_succ_lt_succ this.1, Nat.lt_of_succ_lt_succ this.2⟩
        let j' : Fin (min as.length bs.length) := ⟨j.val, this⟩
        have h := ih j'
        simp [j'] at h
        exact h

/-- Specification: The result has the same length as inputs -/
theorem multiply_length {n : Nat} (a b : Vector Int n) :
  (multiply a b).toList.length = n := by
  simp [multiply, Vector.toList_length]

/-- Specification: Each element is the product of corresponding input elements -/
theorem multiply_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (multiply a b)[i] = a[i] * b[i] := by
  intro i
  simp [multiply, Vector.get_mk]
  have h_len : (List.zipWith (· * ·) a.toList b.toList).length = n := by
    rw [zipWith_length]
    simp [Vector.toList_length]
  have i_bound : i.val < (List.zipWith (· * ·) a.toList b.toList).length := by
    rw [h_len]
    exact i.isLt
  have i_cast : Fin (List.zipWith (· * ·) a.toList b.toList).length := ⟨i.val, i_bound⟩
  rw [List.get_zipWith (· * ·) a.toList b.toList i_cast]
  simp [Vector.get_def]
  have min_eq : min a.toList.length b.toList.length = n := by
    simp [Vector.toList_length]
  have eq1 : i_cast.cast (Nat.min_le_left a.toList.length b.toList.length) = ⟨i.val, by simp [Vector.toList_length]; exact i.isLt⟩ := by
    simp [Fin.cast, Vector.toList_length]
  have eq2 : i_cast.cast (Nat.min_le_right a.toList.length b.toList.length) = ⟨i.val, by simp [Vector.toList_length]; exact i.isLt⟩ := by
    simp [Fin.cast, Vector.toList_length]
  rw [eq1, eq2]
  simp [Vector.get_def]

end DafnySpecs.NpMultiply