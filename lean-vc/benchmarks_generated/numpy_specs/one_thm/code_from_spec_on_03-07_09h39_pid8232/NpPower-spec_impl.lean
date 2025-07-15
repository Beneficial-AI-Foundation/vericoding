namespace NpPower

def power {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] ^ b[i])

theorem power_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (power a b).toList.length = n ∧
  ∀ i : Fin n, (power a b)[i] = (a[i]) ^ (b[i]) := by
  constructor
  · simp [power, Vector.ofFn]
  · intro i
    simp [power, Vector.ofFn]

end NpPower