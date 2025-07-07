/-
# NumPy Reshape Specification

Port of np_reshape.dfy to Lean 4
-/

namespace DafnySpecs.NpReshape

-- LLM HELPER
def Matrix (α : Type) (m k : Nat) : Type := Fin m → Fin k → α

-- LLM HELPER
def Matrix.toList {α : Type} {m k : Nat} (mat : Matrix α m k) : List α :=
  (List.range m).flatMap fun i => (List.range k).map fun j => 
    mat ⟨i, by simp; exact List.mem_range.mp (List.mem_of_mem_range rfl)⟩ 
        ⟨j, by simp; exact List.mem_range.mp (List.mem_of_mem_range rfl)⟩

-- LLM HELPER
def vectorToMatrix {n m k : Nat} (a : Vector Int n) (hm : m > 0) (hk : k > 0) (h : n = m * k) : Matrix Int m k :=
  fun i j => a[i.val * k + j.val]!

/-- Reshape vector to new dimensions -/
def reshape {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2) : Matrix Int m k := 
  if hm : m > 0 then
    if hk : k > 0 then
      if h : n = m * k then
        vectorToMatrix a hm hk h
      else
        fun _ _ => 0
    else
      fun _ _ => 0
  else
    fun _ _ => 0

-- LLM HELPER
lemma matrix_toList_length {m k : Nat} (mat : Matrix Int m k) : 
  mat.toList.length = m * k := by
  simp only [Matrix.toList]
  rw [List.length_flatMap]
  simp only [List.sum_map_count, List.length_range]
  ring

-- LLM HELPER
lemma pos_of_prod_eq_succ {m k n : Nat} (h : n = m * k) (hn : n > 0) : m > 0 ∧ k > 0 := by
  constructor
  · by_contra h_neg
    simp at h_neg
    rw [h] at hn
    simp [h_neg] at hn
  · by_contra h_neg
    simp at h_neg
    rw [h] at hn
    simp [h_neg, mul_zero] at hn

/-- Specification: Element count is preserved -/
theorem reshape_count {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := @reshape n m k a newshape
  ret.toList.length = n := by
  simp only [reshape]
  by_cases hn : n = 0
  · simp [hn] at h2
    simp [h2]
    rw [hn]
  · have hn_pos : n > 0 := Nat.pos_of_ne_zero hn
    have ⟨hm, hk⟩ := pos_of_prod_eq_succ h2 hn_pos
    simp [hm, hk, h2]
    rw [matrix_toList_length]
    exact h2.symm

/-- Specification: Elements are correctly mapped -/
theorem reshape_spec {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := @reshape n m k a newshape
  ∀ i j : Fin m, ∀ jf : Fin k, ret i jf = a[i.val * k + jf.val]! := by
  intro i jf
  simp only [reshape]
  by_cases hn : n = 0
  · simp [hn] at h2
    simp [h2]
    have : m = 0 := by
      rw [←h2, hn]
      simp
    have : False := by
      have : i.val < m := i.isLt
      rw [this] at *
      simp at *
    contradiction
  · have hn_pos : n > 0 := Nat.pos_of_ne_zero hn
    have ⟨hm, hk⟩ := pos_of_prod_eq_succ h2 hn_pos
    simp [hm, hk, h2]
    simp only [vectorToMatrix]
    rfl

end DafnySpecs.NpReshape