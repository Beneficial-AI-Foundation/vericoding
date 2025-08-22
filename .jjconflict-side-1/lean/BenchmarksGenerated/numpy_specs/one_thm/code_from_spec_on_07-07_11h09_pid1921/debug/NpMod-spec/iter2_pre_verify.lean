namespace NpMod

def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }

def mod {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n := 
  Vector.ofFn (fun i : Fin n => a[i] % b.val[i])

-- LLM HELPER
lemma vector_ofFn_length {n : Nat} (f : Fin n → Int) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList_mk]

-- LLM HELPER
lemma vector_ofFn_get {n : Nat} (f : Fin n → Int) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get_mk]

theorem mod_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (mod a b).toList.length = n ∧
  ∀ i : Fin n, (mod a b)[i] = a[i] % (b.val[i]) := by
  constructor
  · simp [mod, Vector.ofFn, Vector.toList_mk]
  · intro i
    simp [mod, Vector.ofFn, Vector.get_mk]

end NpMod