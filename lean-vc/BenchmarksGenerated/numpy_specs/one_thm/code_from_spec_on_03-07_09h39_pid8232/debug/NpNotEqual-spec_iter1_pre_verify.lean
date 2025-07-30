namespace NpNotEqual

def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] ≠ b[i])

/- LLM HELPER -/
lemma vector_ofFn_length {n : Nat} (f : Fin n → Bool) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList_mk]

/- LLM HELPER -/
lemma vector_ofFn_get {n : Nat} (f : Fin n → Bool) (i : Fin n) : 
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get_mk]

theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) := by
  constructor
  · exact vector_ofFn_length (fun i => a[i] ≠ b[i])
  · intro i
    exact vector_ofFn_get (fun i => a[i] ≠ b[i]) i

end NpNotEqual