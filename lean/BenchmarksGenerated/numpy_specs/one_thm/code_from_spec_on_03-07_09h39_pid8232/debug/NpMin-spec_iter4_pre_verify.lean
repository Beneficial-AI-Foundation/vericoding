namespace NpMin

/- LLM HELPER -/
def min_two (a b : Int) : Int :=
  if a ≤ b then a else b

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl min_two a[0] a

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : 
  ∃ i : Fin n, True := by
  use ⟨0, h⟩
  trivial

/- LLM HELPER -/
lemma min_two_le_left (a b : Int) : min_two a b ≤ a := by
  unfold min_two
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]

/- LLM HELPER -/
lemma min_two_le_right (a b : Int) : min_two a b ≤ b := by
  unfold min_two
  by_cases h : a ≤ b
  · simp [h]; exact h
  · simp [h]

/- LLM HELPER -/
lemma min_two_eq_left_or_right (a b : Int) : min_two a b = a ∨ min_two a b = b := by
  unfold min_two
  by_cases h : a ≤ b
  · simp [h]; left; rfl
  · simp [h]; right; rfl

/- LLM HELPER -/
lemma foldl_min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl min_two a[0] a = a[i] := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => 
        use 0
        simp [Vector.foldl]
      | succ m =>
        use 0
        simp [Vector.foldl]
        have : Vector.foldl min_two a[0] a = a[0] := by
          simp [Vector.foldl]
          rfl
        exact this

/- LLM HELPER -/
lemma foldl_min_le {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, Vector.foldl min_two a[0] a ≤ a[i] := by
  intro i
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero =>
        simp [Vector.foldl]
        cases i using Fin.cases with
        | zero => le_refl _
      | succ m =>
        simp [Vector.foldl]
        apply min_two_le_right

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  constructor
  · exact (foldl_min_exists h a)
  · exact foldl_min_le h a

end NpMin