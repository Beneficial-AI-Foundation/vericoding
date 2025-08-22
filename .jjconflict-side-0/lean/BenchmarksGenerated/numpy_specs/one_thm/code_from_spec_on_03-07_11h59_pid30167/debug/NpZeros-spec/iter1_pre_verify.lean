namespace NpZeros

def zeros (n : Nat) : Vector Int n := Vector.replicate n 0

def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows := Vector.replicate rows (Vector.replicate cols 0)

/- LLM HELPER -/
lemma vector_replicate_get (n : Nat) (a : Int) (i : Fin n) :
  (Vector.replicate n a)[i.val] = a := by
  simp [Vector.replicate, Vector.get]

theorem zeros_spec (n : Nat) :
  ∀ i : Fin n, (zeros n)[i.val] = 0 ∧
  ∀ rows cols : Nat, ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i.val][j.val] = 0 := by
  constructor
  · intro i
    simp [zeros, Vector.replicate, Vector.get]
  · intro rows cols i j
    simp [zeros2d, Vector.replicate, Vector.get]

end NpZeros