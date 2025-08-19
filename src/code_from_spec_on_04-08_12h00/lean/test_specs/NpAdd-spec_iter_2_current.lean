namespace NpAdd

def add {n : Nat} (a b : Vector Int n) : Vector Int n := 
  sorry
  Vector.zipWith (· + ·) a b

-- LLM HELPER
lemma Vector.get_zipWith {α β γ : Type*} {n : Nat} (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Fin n) :
  (Vector.zipWith f a b)[i] = f a[i] b[i] := by
  simp [Vector.zipWith, Vector.get_mk]

theorem add_spec {n : Nat} (a b : Vector Int n) :
  (add a b).toList.length = n ∧
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] := by
  constructor
  · simp [add]
  · intro i
    simp [add, Vector.get_zipWith]

end NpAdd