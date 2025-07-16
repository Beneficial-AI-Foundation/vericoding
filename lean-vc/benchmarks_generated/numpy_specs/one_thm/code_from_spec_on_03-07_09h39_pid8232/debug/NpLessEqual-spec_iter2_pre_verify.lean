namespace NpLessEqual

def lessEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.zipWith (fun x y => x ≤ y) a b

theorem lessEqual_spec {n : Nat} (a b : Vector Int n) :
  (lessEqual a b).toList.length = n ∧
  ∀ i : Fin n, (lessEqual a b)[i] = (a[i] ≤ b[i]) := by
  constructor
  · simp [lessEqual]
  · intro i
    simp [lessEqual, Vector.get_zipWith]

end NpLessEqual