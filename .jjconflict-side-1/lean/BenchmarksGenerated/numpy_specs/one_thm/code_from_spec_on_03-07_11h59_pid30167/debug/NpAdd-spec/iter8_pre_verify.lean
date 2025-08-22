namespace NpAdd

def add {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.zipWith (· + ·) a b

/- LLM HELPER -/
lemma vector_zipWith_get {α β γ : Type*} {n : Nat} (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Fin n) :
  (Vector.zipWith f a b)[i] = f a[i] b[i] := by
  simp [Vector.zipWith, Vector.get_mk]

theorem add_spec {n : Nat} (a b : Vector Int n) :
  (add a b).toList.length = n ∧
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] := by
  constructor
  · simp [add, Vector.toList]
  · intro i
    simp [add, vector_zipWith_get]

end NpAdd