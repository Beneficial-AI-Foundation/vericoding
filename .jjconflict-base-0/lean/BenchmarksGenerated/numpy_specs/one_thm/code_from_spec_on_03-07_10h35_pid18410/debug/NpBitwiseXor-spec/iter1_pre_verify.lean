namespace NpBitwiseXor

def bitwiseXor {n : Nat} (a b : Vector Nat n) : Vector Nat n := 
  Vector.ofFn (fun i => a[i] ^^^ b[i])

theorem bitwiseXor_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseXor a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseXor a b)[i] = a[i] ^^^ b[i] := by
  constructor
  · simp [bitwiseXor]
    exact Vector.length_ofFn _ _
  · intro i
    simp [bitwiseXor]
    exact Vector.get_ofFn _ _

end NpBitwiseXor