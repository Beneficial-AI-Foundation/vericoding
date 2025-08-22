namespace NpRemainder

def remainder {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] % b[i])

theorem remainder_spec {n : Nat} (a b : Vector Int n)
  (h : ∀ i : Fin n, b[i] ≠ 0) :
  let ret := remainder a b
  (ret.toList.length = n) ∧
  (∀ i : Fin n, ret[i] = a[i] % b[i]) := by
  constructor
  · simp [remainder]
  · intro i
    simp [remainder]

end NpRemainder