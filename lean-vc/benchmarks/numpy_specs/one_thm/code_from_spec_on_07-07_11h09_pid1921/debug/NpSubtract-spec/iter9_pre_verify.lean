namespace NpSubtract

def subtract {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.zipWith (· - ·) a b

theorem subtract_spec {n : Nat} (a b : Vector Int n) :
  (subtract a b).toList.length = n ∧
  ∀ i : Fin n, (subtract a b)[i] = a[i] - b[i] := by
  constructor
  · simp [subtract, Vector.toList_zipWith]
  · intro i
    simp [subtract, Vector.zipWith_get]

end NpSubtract