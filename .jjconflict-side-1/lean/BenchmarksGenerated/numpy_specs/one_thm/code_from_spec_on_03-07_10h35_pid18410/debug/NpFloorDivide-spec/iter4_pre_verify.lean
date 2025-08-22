namespace NpFloorDivide

def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }

def floorDivide {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n := 
  Vector.ofFn (fun i : Fin n => a[i] / b.val[i])

/- LLM HELPER -/
lemma vector_ofFn_length {n : Nat} (f : Fin n → Int) : (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/- LLM HELPER -/
lemma vector_ofFn_get {n : Nat} (f : Fin n → Int) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get]

theorem floorDivide_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (floorDivide a b).toList.length = n ∧
  ∀ i : Fin n, (floorDivide a b)[i] = a[i] / (b.val[i]) := by
  constructor
  · exact vector_ofFn_length (fun i => a[i] / b.val[i])
  · intro i
    exact vector_ofFn_get (fun i => a[i] / b.val[i]) i

end NpFloorDivide