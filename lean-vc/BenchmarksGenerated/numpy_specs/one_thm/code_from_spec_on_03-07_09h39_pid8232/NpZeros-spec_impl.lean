namespace NpZeros

def zeros (n : Nat) : Vector Int n := Vector.replicate n 0

def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows := Vector.replicate rows (Vector.replicate cols 0)

/- LLM HELPER -/
lemma vector_get_replicate {α : Type*} (n : Nat) (a : α) (i : Fin n) : 
  (Vector.replicate n a)[i] = a := by
  simp [Vector.get_eq_get, Vector.replicate_get]

theorem zeros_spec (n : Nat) :
  ∀ i : Fin n, (zeros n)[i] = 0 ∧
  ∀ rows cols : Nat, ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i][j] = 0 := by
  intro i
  constructor
  · simp [zeros, Vector.get_eq_get, Vector.replicate_get]
  · intro rows cols i j
    simp [zeros2d, Vector.get_eq_get, Vector.replicate_get]

end NpZeros