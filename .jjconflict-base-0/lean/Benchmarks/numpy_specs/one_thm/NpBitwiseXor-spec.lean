namespace NpBitwiseXor

def bitwiseXor {n : Nat} (a b : Vector Nat n) : Vector Nat n := sorry

theorem bitwiseXor_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseXor a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseXor a b)[i] = a[i] ^^^ b[i] := sorry

end NpBitwiseXor 