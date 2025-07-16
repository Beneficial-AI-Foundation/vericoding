namespace NpMultiply

def multiply {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] * b[i])

theorem multiply_spec {n : Nat} (a b : Vector Int n) :
  (multiply a b).toList.length = n ∧
  ∀ i : Fin n, (multiply a b)[i] = a[i] * b[i] := by
  constructor
  · simp [multiply, Vector.toList_ofFn]
  · intro i
    simp [multiply, Vector.get_ofFn]

end NpMultiply