/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/- LLM HELPER -/
def list_maximum (l : List Int) (h : l ≠ []) : Int :=
  List.foldl max (l.head h) l

/- LLM HELPER -/
lemma list_maximum_mem (l : List Int) (h : l ≠ []) : list_maximum l h ∈ l := by
  unfold list_maximum
  have : l.head h ∈ l := List.head_mem h
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp [List.foldl]
    if h_eq : xs = [] then
      simp [h_eq, List.head]
      exact List.mem_cons_self x []
    else
      simp at ih
      have ih' := ih h_eq
      cases' List.mem_cons.mp ih' with h1 h2
      · simp [List.head] at h1
        rw [← h1]
        exact List.mem_cons_self x xs
      · exact List.mem_cons_of_mem x h2

/- LLM HELPER -/
lemma list_maximum_ge (l : List Int) (h : l ≠ []) (x : Int) :
  x ∈ l → x ≤ list_maximum l h := by
  intro h_mem
  unfold list_maximum
  induction l with
  | nil => contradiction
  | cons y ys ih =>
    simp [List.foldl]
    cases' List.mem_cons.mp h_mem with h1 h2
    · rw [h1]
      if h_eq : ys = [] then
        simp [h_eq, List.head]
        exact le_max_left y (List.foldl max y [])
      else
        simp [List.head]
        exact le_max_left y (List.foldl max y ys)
    · if h_eq : ys = [] then
        simp [h_eq] at h2
      else
        simp [List.head]
        have ih' := ih h_eq h2
        exact le_trans ih' (le_max_right y (List.foldl max y ys))

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  list_maximum a.toList (by
    intro h_empty
    have : a.toList.length = 0 := List.length_eq_zero_iff.mpr h_empty
    rw [Vector.length_toList] at this
    exact Nat.ne_zero_of_lt h this)

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero_iff.mpr h_empty
  rw [Vector.length_toList] at this
  exact Nat.ne_zero_of_lt h this

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] := by
  unfold max
  have h_mem := list_maximum_mem a.toList (vector_nonempty h a)
  rw [Vector.mem_toList_iff] at h_mem
  exact h_mem

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  intro i
  unfold max
  apply list_maximum_ge
  rw [Vector.mem_toList_iff]
  exact ⟨i, rfl⟩

end DafnySpecs.NpMax