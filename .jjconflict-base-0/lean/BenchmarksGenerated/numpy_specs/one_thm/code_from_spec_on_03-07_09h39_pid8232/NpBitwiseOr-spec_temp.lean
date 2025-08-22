namespace NpBitwiseOr

def bitwiseOr {n : Nat} (a b : Vector Nat n) : Vector Nat n := 
  Vector.zipWith (· ||| ·) a b

/- LLM HELPER -/
lemma vector_zipWith_get {α β γ : Type*} {n : Nat} (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Fin n) :
  (Vector.zipWith f a b)[i] = f a[i] b[i] := by
  simp [Vector.zipWith, Vector.get_mk]

theorem bitwiseOr_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseOr a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseOr a b)[i] = a[i] ||| b[i] := by
  constructor
  · simp [bitwiseOr, Vector.zipWith]
  · intro i
    simp [bitwiseOr, vector_zipWith_get]

end NpBitwiseOr