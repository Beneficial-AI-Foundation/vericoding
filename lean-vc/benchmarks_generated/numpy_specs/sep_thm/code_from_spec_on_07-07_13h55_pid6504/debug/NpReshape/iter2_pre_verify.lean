/-
# NumPy Reshape Specification

Port of np_reshape.dfy to Lean 4
-/

namespace DafnySpecs.NpReshape

-- LLM HELPER
def Matrix (α : Type) (m k : Nat) : Type := Fin m → Fin k → α

-- LLM HELPER
def Matrix.toList {α : Type} {m k : Nat} (mat : Matrix α m k) : List α :=
  (List.range m).bind fun i => (List.range k).map fun j => mat ⟨i, Nat.lt_of_mem_range (List.mem_range.mp (List.mem_range.mpr i.2))⟩ ⟨j, Nat.lt_of_mem_range (List.mem_range.mp (List.mem_range.mpr j.2))⟩

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
  simp [Matrix.toList]
  rw [List.length_bind]
  simp [List.sum_map_count]
  ring

/-- Specification: Element count is preserved -/
theorem reshape_count {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := @reshape n m k a newshape
  ret.toList.length = n := by
  simp [reshape]
  rw [matrix_toList_length]
  exact h2.symm

/-- Specification: Elements are correctly mapped -/
theorem reshape_spec {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := @reshape n m k a newshape
  ∀ i j : Fin m, ∀ jf : Fin k, ret i jf = a[i.val * k + jf.val]! := by
  intro i jf
  simp [reshape]
  split_ifs with hm hk hn
  · simp [vectorToMatrix]
  · simp
  · simp
  · simp

end DafnySpecs.NpReshape