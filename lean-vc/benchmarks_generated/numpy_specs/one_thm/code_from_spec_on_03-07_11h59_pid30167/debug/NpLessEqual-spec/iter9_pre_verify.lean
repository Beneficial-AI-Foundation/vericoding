namespace NpLessEqual

def lessEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] ≤ b[i])

theorem lessEqual_spec {n : Nat} (a b : Vector Int n) :
  (lessEqual a b).toList.length = n ∧
  ∀ i : Fin n, (lessEqual a b)[i] = (a[i] ≤ b[i]) := by
  constructor
  · simp [lessEqual, Vector.toList_ofFn]
  · intro i
    simp [lessEqual, Vector.get_ofFn]

end NpLessEqual