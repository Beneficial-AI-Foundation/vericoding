namespace NpNotEqual

def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] ≠ b[i])

/- LLM HELPER -/
lemma Vector.toList_length_ofFn {n : Nat} (f : Fin n → Bool) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/- LLM HELPER -/
lemma Vector.get_ofFn {n : Nat} (f : Fin n → Bool) (i : Fin n) : 
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get]

theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) := by
  constructor
  · exact Vector.toList_length_ofFn (fun i => a[i] ≠ b[i])
  · intro i
    exact Vector.get_ofFn (fun i => a[i] ≠ b[i]) i

end NpNotEqual