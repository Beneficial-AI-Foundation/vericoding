namespace NpBitwiseOr

def bitwiseOr {n : Nat} (a b : Vector Nat n) : Vector Nat n := 
  Vector.ofFn (fun i => a[i] ||| b[i])

theorem bitwiseOr_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseOr a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseOr a b)[i] = a[i] ||| b[i] := by
  constructor
  · simp [bitwiseOr]
  · intro i
    simp [bitwiseOr]

end NpBitwiseOr