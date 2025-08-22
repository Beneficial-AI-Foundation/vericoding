/-
# NumPy Add Specification

Port of np_add.dfy to Lean 4
-/

namespace DafnySpecs.NpAdd

/-- Element-wise addition of two vectors -/
def add {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.mk (List.zipWith (· + ·) a.toList b.toList)

/- LLM HELPER -/
lemma zipWith_add_length {n : Nat} (a b : Vector Int n) :
  (List.zipWith (· + ·) a.toList b.toList).length = n := by
  rw [List.length_zipWith]
  simp [Vector.toList_length]

/-- Specification: The result has the same length as inputs -/
theorem add_length {n : Nat} (a b : Vector Int n) :
  (add a b).toList.length = n := by
  unfold add
  simp [Vector.toList_mk]
  exact zipWith_add_length a b

/- LLM HELPER -/
lemma zipWith_add_get {n : Nat} (a b : Vector Int n) (i : Fin n) :
  (List.zipWith (· + ·) a.toList b.toList).get ⟨i.val, by rw [List.length_zipWith]; simp [Vector.toList_length]; exact i.isLt⟩ = a[i] + b[i] := by
  rw [List.get_zipWith]
  simp [Vector.get_eq_get]

/-- Specification: Each element is the sum of corresponding input elements -/
theorem add_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] := by
  intro i
  unfold add
  simp [Vector.get_mk]
  exact zipWith_add_get a b i

end DafnySpecs.NpAdd