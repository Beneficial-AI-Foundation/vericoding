namespace NpPower

def power {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] ^ b[i])

/- LLM HELPER -/
lemma vector_ofFn_length {n : Nat} (f : Fin n → Int) : (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/- LLM HELPER -/
lemma vector_ofFn_get {n : Nat} (f : Fin n → Int) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn]

theorem power_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (power a b).toList.length = n ∧
  ∀ i : Fin n, (power a b)[i] = (a[i]) ^ (b[i]) := by
  constructor
  · simp [power]
    exact vector_ofFn_length (fun i => a[i] ^ b[i])
  · intro i
    simp [power]
    exact vector_ofFn_get (fun i => a[i] ^ b[i]) i

end NpPower