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
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero => 
      use 0
      simp [Vector.foldl]
    | succ m =>
      have h' : m + 1 > 0 := Nat.succ_pos _
      sorry

/- LLM HELPER -/
lemma foldl_min_le {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, Vector.foldl Int.min a[0] a ≤ a[i] := by
  intro i
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      simp [Vector.foldl]
      cases i using Fin.cases with
      | zero => rfl
    | succ m =>
      sorry

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  constructor
  · exact foldl_min_exists h a
  · exact foldl_min_le h a

end NpMin