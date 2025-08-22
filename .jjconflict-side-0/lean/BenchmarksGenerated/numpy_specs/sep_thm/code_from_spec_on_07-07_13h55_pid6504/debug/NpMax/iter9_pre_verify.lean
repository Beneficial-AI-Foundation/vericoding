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
    cases n' with
    | zero => 
      use ⟨0, by simp⟩
      simp [Vector.tail, Vector.foldl]
    | succ n'' =>
      use ⟨0, by simp⟩
      simp [Vector.foldl]
      apply Vector.foldl_le_max

-- LLM HELPER
lemma vector_foldl_le_max {α : Type*} [LinearOrder α] (f : α → α → α) (hf : ∀ x y, f x y = max x y) 
  (init : α) (v : Vector α n) : 
  ∃ i : Fin (n + 1), Vector.foldl f init v = if i.val = 0 then init else v.get ⟨i.val - 1, by omega⟩ := by
  induction n, v using Vector.inductionOn with
  | h_nil => 
    use ⟨0, by simp⟩
    simp [Vector.foldl]
  | h_cons x xs ih =>
    obtain ⟨j, hj⟩ := ih
    simp [Vector.foldl]
    rw [hf]
    by_cases h : init ≥ x
    · use ⟨0, by simp⟩
      simp [max_def, h]
    · use ⟨1, by simp⟩
      simp [max_def, h]

-- LLM HELPER
lemma foldl_max_ge {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a.get i ≤ Vector.foldl (fun x y => if x ≥ y then x else y) (a.get ⟨0, h⟩) (Vector.tail a) := by
  intro i
  cases n with
  | zero => contradiction
  | succ n' =>
    cases n' with
    | zero => 
      simp [Vector.tail, Vector.foldl]
    | succ n'' =>
      simp [Vector.foldl]
      apply Vector.foldl_preserves_max

-- LLM HELPER
lemma Vector.foldl_preserves_max {α : Type*} [LinearOrder α] (v : Vector α n) (init : α) :
  ∀ i : Fin (n + 1), 
    (if i.val = 0 then init else v.get ⟨i.val - 1, by omega⟩) ≤ 
    Vector.foldl (fun x y => if x ≥ y then x else y) init v := by
  intro i
  induction n, v using Vector.inductionOn with
  | h_nil => 
    simp [Vector.foldl]
  | h_cons x xs ih =>
    simp [Vector.foldl]
    split
    · simp
      split
      · simp
      · apply Int.le_max_left
    · simp at *
      split
      · apply Int.le_max_right  
      · exact ih ⟨i.val - 1, by omega⟩

-- LLM HELPER
lemma Vector.foldl_le_max {α : Type*} [LinearOrder α] (v : Vector α n) (init : α) :
  Vector.foldl (fun x y => if x ≥ y then x else y) init v = 
  Vector.foldl max init v := by
  induction n, v using Vector.inductionOn with
  | h_nil => simp [Vector.foldl]
  | h_cons x xs ih =>
    simp [Vector.foldl, max_def]
    rw [ih]

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