namespace NpZeros

def zeros (n : Nat) : Vector Int n := Vector.replicate n 0

def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows := Vector.replicate rows (Vector.replicate cols 0)

/- LLM HELPER -/
lemma vector_replicate_get (n : Nat) (a : Int) (i : Fin n) :
  (Vector.replicate n a)[i] = a := by
  simp [Vector.replicate, Vector.get]

/- LLM HELPER -/
lemma vector_replicate_2d_get (rows cols : Nat) (a : Int) (i : Fin rows) (j : Fin cols) :
  (Vector.replicate rows (Vector.replicate cols a))[i][j] = a := by
  simp [Vector.replicate, Vector.get]

theorem zeros_spec (n : Nat) :
  ∀ i : Fin n, (zeros n)[i] = 0 ∧
  ∀ rows cols : Nat, ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i][j] = 0 := by
  intro i
  constructor
  · exact vector_replicate_get n 0 i
  · intro rows cols i j
    exact vector_replicate_2d_get rows cols 0 i j

end NpZeros