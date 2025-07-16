namespace NpGreaterEqual

def greaterEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.zipWith (fun x y => x ≥ y) a b

theorem greaterEqual_spec {n : Nat} (a b : Vector Int n) :
  (greaterEqual a b).toList.length = n ∧
  ∀ i : Fin n, (greaterEqual a b)[i] = (a[i] ≥ b[i]) := by
  constructor
  · simp [greaterEqual]
  · intro i
    simp [greaterEqual]
    rfl

end NpGreaterEqual