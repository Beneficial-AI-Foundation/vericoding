/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.foldl Int.max (a[0])

-- LLM HELPER
lemma max_def {n : Nat} (h : n > 0) (a : Vector Int n) :
  max h a = a.foldl Int.max (a[0]) := rfl

-- LLM HELPER
lemma foldl_max_ge_init {n : Nat} (a : Vector Int n) (init : Int) :
  init ≤ a.foldl Int.max init := by
  induction a using Vector.inductionOn with
  | nil => simp [Vector.foldl]
  | cons head tail ih =>
    simp [Vector.foldl]
    have : init ≤ Int.max init head := Int.le_max_left init head
    exact Int.le_trans this (ih (Int.max init head))

-- LLM HELPER
lemma foldl_max_ge_all {n : Nat} (a : Vector Int n) (init : Int) (i : Fin n) :
  a[i] ≤ a.foldl Int.max init := by
  induction n, a using Vector.inductionOn generalizing i with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
    simp [Vector.foldl]
    cases' i using Fin.cases with i'
    · simp [Vector.get]
      exact Int.le_trans (Int.le_max_right init head) (foldl_max_ge_init tail (Int.max init head))
    · simp [Vector.get]
      exact ih i'

-- LLM HELPER
lemma foldl_max_exists {n : Nat} (a : Vector Int n) (init : Int) :
  ∃ i : Fin (n + 1), a.foldl Int.max init = if i = 0 then init else a[i.pred (Fin.pos_iff_ne_zero.mpr (Fin.ne_of_gt (Fin.pos_iff_ne_zero.mp (Nat.zero_lt_of_ne_zero (Fin.ne_of_gt (Nat.zero_lt_succ n) |>.symm)))))] ∨ 
    (∃ j : Fin n, a.foldl Int.max init = a[j]) := by
  induction n, a using Vector.inductionOn with
  | nil => 
    use 0
    simp [Vector.foldl]
  | cons head tail ih =>
    simp [Vector.foldl]
    by_cases h : init ≤ head
    · have : Int.max init head = head := Int.max_def.symm ▸ if_neg (not_lt.mpr h)
      rw [this]
      right
      use 0
      simp [Vector.get]
    · have : Int.max init head = init := Int.max_def.symm ▸ if_pos (lt_of_not_ge h)
      rw [this]
      left
      use 0
      simp

-- LLM HELPER
lemma vector_nonempty_has_element {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, a[i] = a[⟨0, h⟩] := by
  use ⟨0, h⟩
  rfl

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] := by
  rw [max_def]
  induction n, a using Vector.inductionOn with
  | nil => contradiction
  | cons head tail ih =>
    simp [Vector.foldl]
    cases' n with n'
    · simp [Vector.foldl]
      use 0
      simp [Vector.get]
    · have h' : n' + 1 > 0 := Nat.succ_pos n'
      by_cases hc : a[⟨0, h⟩] ≤ head
      · have : Int.max a[⟨0, h⟩] head = head := Int.max_def.symm ▸ if_neg (not_lt.mpr hc)
        rw [this]
        use 0
        simp [Vector.get]
      · have : Int.max a[⟨0, h⟩] head = a[⟨0, h⟩] := Int.max_def.symm ▸ if_pos (lt_of_not_ge hc)
        rw [this]
        use ⟨0, h⟩
        rfl

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  intro i
  rw [max_def]
  exact foldl_max_ge_all (a.tail) a[⟨0, h⟩] i

end DafnySpecs.NpMax