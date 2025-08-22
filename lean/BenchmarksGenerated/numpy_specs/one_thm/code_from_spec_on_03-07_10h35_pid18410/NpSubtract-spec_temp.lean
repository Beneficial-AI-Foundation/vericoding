namespace NpSubtract

def subtract {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] - b[i])

theorem subtract_spec {n : Nat} (a b : Vector Int n) :
  (subtract a b).toList.length = n ∧
  ∀ i : Fin n, (subtract a b)[i] = a[i] - b[i] := by
  constructor
  · simp [subtract, Vector.toList_ofFn]
  · intro i
    simp [subtract, Vector.ofFn_get]

end NpSubtract