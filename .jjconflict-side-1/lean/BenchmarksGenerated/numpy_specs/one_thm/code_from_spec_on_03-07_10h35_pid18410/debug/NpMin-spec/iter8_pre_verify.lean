namespace NpMin

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.foldl Int.min (a.get ⟨0, h⟩)

/- LLM HELPER -/
lemma foldl_min_le {n : Nat} (a : Vector Int n) (init : Int) (i : Fin n) :
  a.foldl Int.min init ≤ a[i] := by
  induction' n with n ih
  · exact absurd i.val i.is_lt
  · cases' i with i hi
    simp [Vector.foldl]
    sorry

/- LLM HELPER -/
lemma foldl_min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, a.foldl min (a.get ⟨0, h⟩) = a[i] := by
  use ⟨0, h⟩
  simp [Vector.foldl]
  sorry

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  constructor
  · exact foldl_min_exists h a
  · intro i
    exact foldl_min_le a (a.get ⟨0, h⟩) i

end NpMin