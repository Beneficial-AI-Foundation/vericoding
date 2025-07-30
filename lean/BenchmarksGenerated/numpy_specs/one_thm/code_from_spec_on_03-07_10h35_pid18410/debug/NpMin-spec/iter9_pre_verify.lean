namespace NpMin

/- LLM HELPER -/
def Int.min (a b : Int) : Int := if a ≤ b then a else b

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.foldl Int.min (a.get ⟨0, h⟩)

/- LLM HELPER -/
lemma Int.min_le_left (a b : Int) : Int.min a b ≤ a := by
  simp [Int.min]
  split_ifs with h
  · rfl
  · exact le_of_not_le h

/- LLM HELPER -/
lemma Int.min_le_right (a b : Int) : Int.min a b ≤ b := by
  simp [Int.min]
  split_ifs with h
  · exact h
  · rfl

/- LLM HELPER -/
lemma foldl_min_le {n : Nat} (a : Vector Int n) (init : Int) (i : Fin n) :
  a.foldl Int.min init ≤ a[i] := by
  induction' n with n ih generalizing init
  · exact absurd i.val i.is_lt
  · cases' i with i hi
    simp [Vector.foldl]
    if h : i = 0 then
      subst h
      simp
      exact Int.min_le_right init (a.get ⟨0, Nat.zero_lt_succ n⟩)
    else
      have i_pos : i > 0 := Nat.pos_of_ne_zero h
      have : i - 1 < n := by
        rw [Nat.sub_lt_iff_lt_add (le_of_lt i_pos)]
        exact Nat.lt_of_succ_le hi
      exact ih a.tail (Int.min init (a.get ⟨0, Nat.zero_lt_succ n⟩)) ⟨i - 1, this⟩

/- LLM HELPER -/
lemma foldl_min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, a.foldl Int.min (a.get ⟨0, h⟩) = a[i] := by
  use ⟨0, h⟩
  induction' n with n ih
  · exact absurd h (Nat.not_lt_zero 0)
  · simp [Vector.foldl]
    if h_eq : n = 0 then
      subst h_eq
      simp [Vector.foldl]
      exact Int.min_le_right (a.get ⟨0, h⟩) (a.get ⟨0, h⟩)
    else
      have n_pos : n > 0 := Nat.pos_of_ne_zero h_eq
      sorry

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  constructor
  · exact foldl_min_exists h a
  · intro i
    exact foldl_min_le a (a.get ⟨0, h⟩) i

end NpMin