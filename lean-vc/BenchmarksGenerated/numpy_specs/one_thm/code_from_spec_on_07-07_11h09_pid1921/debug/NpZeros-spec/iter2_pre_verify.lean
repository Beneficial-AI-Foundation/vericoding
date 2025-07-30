namespace NpZeros

def zeros (n : Nat) : Vector Int n := Vector.replicate n 0

def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows := Vector.replicate rows (Vector.replicate cols 0)

theorem zeros_spec (n : Nat) :
  ∀ i : Fin n, (zeros n)[i.val] = 0 ∧
  ∀ rows cols : Nat, ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i.val][j.val] = 0 := by
  intro i
  constructor
  · simp [zeros, Vector.get_replicate]
  · intro rows cols i j
    simp [zeros2d, Vector.get_replicate]

end NpZeros