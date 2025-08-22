namespace NpBitwiseXor

def bitwiseXor {n : Nat} (a b : Vector Nat n) : Vector Nat n := 
  Vector.ofFn (fun i => a[i] ^^^ b[i])

theorem bitwiseXor_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseXor a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseXor a b)[i] = a[i] ^^^ b[i] := by
  constructor
  · simp [bitwiseXor]
  · intro i
    simp [bitwiseXor]

end NpBitwiseXor