namespace NpNotEqual

def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] ≠ b[i])

theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) := by
  constructor
  · simp [notEqual, Vector.toList_ofFn]
  · intro i
    simp [notEqual, Vector.ofFn_get]

end NpNotEqual