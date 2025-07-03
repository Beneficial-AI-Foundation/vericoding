namespace NpAdd

def add {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.zipWith (· + ·) a b

theorem add_spec {n : Nat} (a b : Vector Int n) :
  (add a b).toList.length = n ∧
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] := by
  constructor
  · simp [add, Vector.toList_length_eq]
  · intro i
    simp [add, Vector.get_zipWith]

end NpAdd