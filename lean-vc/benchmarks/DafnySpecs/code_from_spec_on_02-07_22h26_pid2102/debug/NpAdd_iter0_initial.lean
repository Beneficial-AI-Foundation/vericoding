/-
# NumPy Add Specification

Port of np_add.dfy to Lean 4
-/

namespace DafnySpecs.NpAdd

/-- Element-wise addition of two vectors -/
def add {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.mk (List.zipWith (· + ·) a.toList b.toList)

/-- LLM HELPER -/
lemma zipWith_length {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) :
  (List.zipWith f l1 l2).length = min l1.length l2.length := by
  induction l1 generalizing l2 with
  | nil => simp [List.zipWith]
  | cons h1 t1 ih =>
    cases l2 with
    | nil => simp [List.zipWith]
    | cons h2 t2 => simp [List.zipWith, ih]

/-- LLM HELPER -/
lemma zipWith_get {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) 
  (h1 : i < l1.length) (h2 : i < l2.length) :
  (List.zipWith f l1 l2)[i]'(by rw [zipWith_length]; exact Nat.lt_min_of_left_lt h1) = f (l1[i]) (l2[i]) := by
  induction l1 generalizing l2 i with
  | nil => contradiction
  | cons h1 t1 ih =>
    cases l2 with
    | nil => contradiction
    | cons h2 t2 =>
      cases i with
      | zero => simp [List.zipWith]
      | succ i' =>
        simp [List.zipWith]
        apply ih
        · simp at h1; exact Nat.lt_of_succ_lt_succ h1
        · simp at h2; exact Nat.lt_of_succ_lt_succ h2

/-- Specification: The result has the same length as inputs -/
theorem add_length {n : Nat} (a b : Vector Int n) :
  (add a b).toList.length = n := by
  simp [add]
  rw [zipWith_length]
  simp [Vector.toList_length]

/-- Specification: Each element is the sum of corresponding input elements -/
theorem add_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] := by
  intro i
  simp [add, Vector.get]
  rw [zipWith_get]
  · simp [Vector.toList_length]
  · simp [Vector.toList_length]

end DafnySpecs.NpAdd