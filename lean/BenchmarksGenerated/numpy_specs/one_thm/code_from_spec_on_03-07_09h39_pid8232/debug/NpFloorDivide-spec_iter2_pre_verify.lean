namespace NpFloorDivide

def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }

def floorDivide {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n := 
  Vector.ofFn (fun i : Fin n => a[i] / b.val[i])

/- LLM HELPER -/
lemma Vector.ofFn_length {n : Nat} (f : Fin n → Int) : (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList_mk]

/- LLM HELPER -/
lemma Vector.get_ofFn {n : Nat} (f : Fin n → Int) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get_mk]

theorem floorDivide_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (floorDivide a b).toList.length = n ∧
  ∀ i : Fin n, (floorDivide a b)[i] = a[i] / (b.val[i]) := by
  constructor
  · exact Vector.ofFn_length _
  · intro i
    exact Vector.get_ofFn _ i

end NpFloorDivide