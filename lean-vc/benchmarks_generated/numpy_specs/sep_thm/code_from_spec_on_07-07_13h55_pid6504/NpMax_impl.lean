/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl (fun x y => if x ≥ y then x else y) (a.get ⟨0, h⟩) (Vector.tail a)

-- LLM HELPER
lemma vector_tail_length {α : Type*} {n : Nat} (v : Vector α n) : 
  (Vector.tail v).length = n - 1 := by
  cases n with
  | zero => simp [Vector.tail]
  | succ n' => simp [Vector.tail]

-- LLM HELPER
lemma foldl_max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl (fun x y => if x ≥ y then x else y) (a.get ⟨0, h⟩) (Vector.tail a) = a.get i := by
  cases n with
  | zero => contradiction
  | succ n' =>
    use ⟨0, by simp⟩
    induction n' with
    | zero => 
      simp [Vector.tail, Vector.foldl]
    | succ n'' =>
      simp [Vector.foldl, Vector.tail]
      rfl

-- LLM HELPER
lemma foldl_max_ge {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a.get i ≤ Vector.foldl (fun x y => if x ≥ y then x else y) (a.get ⟨0, h⟩) (Vector.tail a) := by
  intro i
  cases n with
  | zero => contradiction
  | succ n' =>
    cases i with
    | mk val isLt =>
      cases val with
      | zero => 
        simp [Vector.foldl]
        have h_foldl : Vector.foldl (fun x y => if x ≥ y then x else y) (a.get ⟨0, h⟩) (Vector.tail a) ≥ a.get ⟨0, h⟩ := by
          induction Vector.tail a using Vector.inductionOn with
          | h_nil => simp [Vector.foldl]
          | h_cons x xs ih =>
            simp [Vector.foldl]
            split
            · assumption
            · simp at *
              linarith
        exact h_foldl
      | succ val' =>
        simp [Vector.foldl]
        induction Vector.tail a using Vector.inductionOn with
        | h_nil => simp [Vector.foldl]
        | h_cons x xs ih =>
          simp [Vector.foldl]
          split
          · simp at *
            have : a.get ⟨val' + 1, isLt⟩ ≤ x := by
              have : ⟨val' + 1, isLt⟩ = ⟨val' + 1, isLt⟩ := rfl
              rfl
            rfl
          · simp at *
            rfl

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a.get i := by
  simp [max]
  exact foldl_max_exists h a

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a.get i ≤ max h a := by
  simp [max]
  exact foldl_max_ge h a

end DafnySpecs.NpMax