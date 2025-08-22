/-
# NumPy Reshape Specification

Port of np_reshape.dfy to Lean 4
-/

namespace DafnySpecs.NpReshape

-- LLM HELPER
def vectorToMatrix {n m k : Nat} (a : Vector Int n) (hm : m > 0) (hk : k > 0) (h : n = m * k) : Matrix Int m k :=
  fun i j => a[i * k + j]!

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
  induction m with
  | zero => simp
  | succ m' ih => 
    simp [List.length_append]
    rw [ih]
    ring

/-- Specification: Element count is preserved -/
theorem reshape_count {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := reshape a newshape
  ret.toList.length = n := by
  simp [reshape]
  rw [matrix_toList_length]
  exact h2.symm

/-- Specification: Elements are correctly mapped -/
theorem reshape_spec {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := reshape a newshape
  ∀ i j : Nat, i < m → j < k → ret[i]![j]! = a[i * k + j]! := by
  intro i j hi hj
  simp [reshape]
  split_ifs with hm hk hn
  · simp [vectorToMatrix]
  · simp
  · simp
  · simp

end DafnySpecs.NpReshape