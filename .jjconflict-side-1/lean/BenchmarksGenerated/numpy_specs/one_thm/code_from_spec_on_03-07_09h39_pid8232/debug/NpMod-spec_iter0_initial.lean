namespace NpMod

def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }

def mod {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] % b.val[i])

theorem mod_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (mod a b).toList.length = n ∧
  ∀ i : Fin n, (mod a b)[i] = a[i] % (b.val[i]) := by
  constructor
  · simp [mod]
  · intro i
    simp [mod]

end NpMod