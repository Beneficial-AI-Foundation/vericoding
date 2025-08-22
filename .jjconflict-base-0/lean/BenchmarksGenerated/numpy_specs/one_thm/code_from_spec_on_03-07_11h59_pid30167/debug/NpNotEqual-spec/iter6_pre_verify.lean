namespace NpNotEqual

def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i : Fin n => a.get i ≠ b.get i)

/- LLM HELPER -/
lemma vector_ofFn_length {n : Nat} (f : Fin n → Bool) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn]

/- LLM HELPER -/
lemma vector_ofFn_get {n : Nat} (f : Fin n → Bool) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.ofFn]

theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b).get i = (a.get i ≠ b.get i) := by
  constructor
  · exact vector_ofFn_length (fun i => a.get i ≠ b.get i)
  · intro i
    exact vector_ofFn_get (fun i => a.get i ≠ b.get i) i

end NpNotEqual