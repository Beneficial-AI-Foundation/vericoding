namespace NpGreater

def greater {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] > b[i])

theorem greater_spec {n : Nat} (a b : Vector Int n) :
  (greater a b).toList.length = n ∧
  ∀ i : Fin n, (greater a b)[i] = (a[i] > b[i]) := by
  constructor
  · simp [greater, Vector.toList_ofFn]
  · intro i
    simp [greater]

end NpGreater