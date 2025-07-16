namespace NpMax

/- LLM HELPER -/
def Int.max (x y : Int) : Int := if x ≤ y then y else x

/- LLM HELPER -/
lemma Int.le_max_left (x y : Int) : x ≤ Int.max x y := by
  simp [Int.max]
  by_cases h : x ≤ y
  · simp [h]
    exact h
  · simp [h]

/- LLM HELPER -/
lemma Int.le_max_right (x y : Int) : y ≤ Int.max x y := by
  simp [Int.max]
  by_cases h : x ≤ y
  · simp [h]
  · simp [h]
    exact Int.le_of_not_ge h

/- LLM HELPER -/
lemma Int.max_def (x y : Int) : Int.max x y = if x ≤ y then y else x := by
  rfl

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl Int.max (a.get ⟨0, h⟩) a

/- LLM HELPER -/
lemma vector_foldl_max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl Int.max (a.get ⟨0, h⟩) a = a.get i := by
  induction n, a using Vector.inductionOn with
  | h_nil => 
    exfalso
    exact Nat.lt_irrefl 0 h
  | h_cons n' v x ih =>
    simp [Vector.foldl]
    cases' n' with n''
    · simp [Vector.foldl]
      use 0
      rfl
    · have h' : n'' + 1 > 0 := Nat.zero_lt_succ n''
      specialize ih h'
      cases' ih with i hi
      by_cases h_max : Int.max x (Vector.foldl Int.max (Vector.head v) v) = x
      · use 0
        simp [h_max]
      · use i.succ
        simp [Vector.foldl]
        rw [Int.max_def] at h_max
        simp at h_max
        rw [if_neg h_max]
        exact hi

/- LLM HELPER -/
lemma vector_foldl_max_ge {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a.get i ≤ Vector.foldl Int.max (a.get ⟨0, h⟩) a := by
  induction n, a using Vector.inductionOn with
  | h_nil => 
    exfalso
    exact Nat.lt_irrefl 0 h
  | h_cons n' v x ih =>
    intro i
    simp [Vector.foldl]
    cases' n' with n''
    · simp [Vector.foldl]
      fin_cases i
      rfl
    · have h' : n'' + 1 > 0 := Nat.zero_lt_succ n''
      specialize ih h'
      cases' i using Fin.cases with i'
      · simp
        exact Int.le_max_left x (Vector.foldl Int.max (Vector.head v) v)
      · simp
        have := ih i'
        exact Int.le_trans this (Int.le_max_right x (Vector.foldl Int.max (Vector.head v) v))

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a.get i ∧
  ∀ i : Fin n, a.get i ≤ max h a := by
  simp [max]
  constructor
  · exact vector_foldl_max_exists h a
  · exact vector_foldl_max_ge h a

end NpMax