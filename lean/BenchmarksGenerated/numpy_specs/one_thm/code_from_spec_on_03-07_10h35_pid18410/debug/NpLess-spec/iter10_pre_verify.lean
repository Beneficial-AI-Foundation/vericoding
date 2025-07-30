namespace NpLess

def less {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] < b[i])

theorem less_spec {n : Nat} (a b : Vector Int n) :
  (less a b).toList.length = n ∧
  ∀ i : Fin n, (less a b)[i] = (a[i] < b[i]) := by
  constructor
  · simp [less, Vector.toList_ofFn]
  · intro i
    simp [less, Vector.ofFn_get]

end NpLess