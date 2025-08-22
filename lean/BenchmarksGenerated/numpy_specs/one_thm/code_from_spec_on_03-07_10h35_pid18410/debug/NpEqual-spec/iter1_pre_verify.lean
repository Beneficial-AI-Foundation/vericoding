namespace NpEqual

def equal {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.zipWith (fun x y => x = y) a b

theorem equal_spec {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n ∧
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) := by
  constructor
  · simp [equal]
    rw [Vector.toList_zipWith]
    simp [Vector.toList_length]
  · intro i
    simp [equal]
    rw [Vector.zipWith_get]

end NpEqual