namespace NpMin

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl Int.min a[0] a

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : 
  ∃ i : Fin n, True := by
  use ⟨0, h⟩
  trivial

/- LLM HELPER -/
lemma foldl_min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl Int.min a[0] a = a[i] := by
  use 0
  simp [Vector.foldl]
  induction n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero => 
      rfl
    | succ m =>
      simp [Vector.foldl]
      rw [Int.min_comm]
      simp [Int.min_self]

/- LLM HELPER -/
lemma foldl_min_le {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, Vector.foldl Int.min a[0] a ≤ a[i] := by
  intro i
  induction n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero =>
      simp [Vector.foldl]
      cases i using Fin.cases with
      | zero => le_refl _
    | succ m =>
      simp [Vector.foldl]
      apply Int.min_le_right

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  constructor
  · exact (foldl_min_exists h a)
  · exact foldl_min_le h a

end NpMin