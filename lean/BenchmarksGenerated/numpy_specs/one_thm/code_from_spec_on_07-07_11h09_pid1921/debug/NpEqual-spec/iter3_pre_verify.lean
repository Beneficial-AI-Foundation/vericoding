namespace NpEqual

def equal {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] = b[i])

theorem equal_spec {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n ∧
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) := by
  constructor
  · simp [equal, Vector.toList_ofFn]
  · intro i
    simp [equal, Vector.get_ofFn]

end NpEqual