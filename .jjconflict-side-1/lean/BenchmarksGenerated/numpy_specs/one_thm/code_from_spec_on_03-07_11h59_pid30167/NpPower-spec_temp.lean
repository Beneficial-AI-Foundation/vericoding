namespace NpPower

def power {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] ^ b[i])

/- LLM HELPER -/
lemma Vector.ofFn_length {n : Nat} {α : Type*} (f : Fin n → α) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/- LLM HELPER -/
lemma Vector.ofFn_get {n : Nat} {α : Type*} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get]

theorem power_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (power a b).toList.length = n ∧
  ∀ i : Fin n, (power a b)[i] = (a[i]) ^ (b[i]) := by
  constructor
  · exact Vector.ofFn_length (fun i => a[i] ^ b[i])
  · intro i
    exact Vector.ofFn_get (fun i => a[i] ^ b[i]) i

end NpPower