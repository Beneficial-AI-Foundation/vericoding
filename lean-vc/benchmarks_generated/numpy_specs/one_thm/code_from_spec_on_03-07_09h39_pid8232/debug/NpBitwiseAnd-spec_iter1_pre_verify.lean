namespace NpBitwiseAnd

def bitwiseAnd {n : Nat} (a b : Vector Nat n) : Vector Nat n := 
  Vector.zipWith (· &&& ·) a b

theorem bitwiseAnd_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseAnd a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseAnd a b)[i] = a[i] &&& b[i] := by
  constructor
  · simp [bitwiseAnd, Vector.toList_zipWith]
  · intro i
    simp [bitwiseAnd, Vector.get_zipWith]

end NpBitwiseAnd