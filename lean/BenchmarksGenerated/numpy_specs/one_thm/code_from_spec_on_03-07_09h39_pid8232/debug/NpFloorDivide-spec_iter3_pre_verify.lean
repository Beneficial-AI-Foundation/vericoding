namespace NpFloorDivide

def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }

def floorDivide {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n := 
  Vector.ofFn (fun i : Fin n => a[i] / b.val[i])

theorem floorDivide_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (floorDivide a b).toList.length = n ∧
  ∀ i : Fin n, (floorDivide a b)[i] = a[i] / (b.val[i]) := by
  constructor
  · simp [floorDivide]
  · intro i
    simp [floorDivide]

end NpFloorDivide