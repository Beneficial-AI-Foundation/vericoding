namespace NpEqual

def equal {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.zipWith (fun x y => x = y) a b

theorem equal_spec {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n ∧
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) := by
  constructor
  · simp [equal]
    exact Vector.length_zipWith _ _ _
  · intro i
    simp [equal]
    exact Vector.zipWith_get _ _ _ _

end NpEqual