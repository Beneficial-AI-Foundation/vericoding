namespace NpLess

def less {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.zipWith (fun x y => x < y) a b

theorem less_spec {n : Nat} (a b : Vector Int n) :
  (less a b).toList.length = n ∧
  ∀ i : Fin n, (less a b)[i] = (a[i] < b[i]) := by
  constructor
  · simp [less]
  · intro i
    simp [less, Vector.zipWith]

end NpLess