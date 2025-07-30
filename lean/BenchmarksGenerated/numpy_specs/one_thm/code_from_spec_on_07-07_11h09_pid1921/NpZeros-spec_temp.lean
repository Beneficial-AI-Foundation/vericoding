namespace NpZeros

def zeros (n : Nat) : Vector Int n := Vector.replicate n 0

def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows := Vector.replicate rows (Vector.replicate cols 0)

-- LLM HELPER
lemma vector_get_replicate {α : Type*} {n : Nat} (a : α) (i : Fin n) :
  (Vector.replicate n a).get i = a := by
  rfl

theorem zeros_spec (n : Nat) :
  ∀ i : Fin n, (zeros n)[i.val] = 0 ∧
  ∀ rows cols : Nat, ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i.val][j.val] = 0 := by
  intro i
  constructor
  · simp [zeros]
    rw [vector_get_replicate]
  · intro rows cols i j
    simp [zeros2d]
    rw [vector_get_replicate]
    rw [vector_get_replicate]

end NpZeros