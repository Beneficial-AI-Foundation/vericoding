/-
# NumPy Sum Specification

Port of np_sum.dfy to Lean 4
-/

namespace DafnySpecs.NpSum

/-- LLM HELPER -/
def sumRange (l : List Int) : Int := l.foldl (· + ·) 0

/-- Sum of all elements in a vector -/
def sum {n : Nat} (a : Vector Int n) : Int := sumRange a.toList

/-- Helper function: sum of elements from start to end (exclusive) -/
def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≥ finish ∨ finish > n then 0 
  else sumRange ((List.range (finish - start)).map (fun i => a[start + i]'(by
    have h1 : i < finish - start := List.mem_range.mp (List.get_mem _ _)
    have h2 : start + i < start + (finish - start) := Nat.add_lt_add_left h1 start
    have h3 : start + (finish - start) = finish := by
      rw [Nat.add_sub_cancel']
      exact Nat.le_of_not_gt (fun h => by
        cases' Nat.lt_or_ge start finish with h' h'
        · exact absurd h' (Nat.not_lt.mpr (Nat.le_of_lt h))
        · exact Nat.not_lt.mpr h' h)
    rw [h3] at h2
    exact Nat.lt_of_lt_of_le h2 (Nat.le_refl _))))

/-- LLM HELPER -/
lemma sumArray_zero {n : Nat} (a : Vector Int n) (start : Nat) :
  sumArray a start start = 0 := by
  simp [sumArray]

/-- LLM HELPER -/
lemma sumArray_bounds {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h : finish > n) : sumArray a start finish = 0 := by
  simp [sumArray, h]

/-- LLM HELPER -/
lemma sumArray_valid_helper {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  ¬(start ≥ finish ∨ finish > n) := by
  simp [Nat.not_le.mpr (Nat.lt_of_le_of_ne h_start (fun h => by
    rw [h] at h_start
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_ne h_start h.symm))), 
    Nat.not_lt.mpr h_finish]

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  simp [sumRange]
  rw [Vector.toList_eq]
  congr 1
  ext i
  simp
  rw [List.get_range]
  congr
  simp [Nat.zero_add]

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by
    have h1 : i < finish - start := by
      apply List.mem_range.mp
      sorry
    have h2 : start + i < n := by
      have : start + i < start + (finish - start) := Nat.add_lt_add_left h1 start
      rw [Nat.add_sub_cancel' h_start] at this
      exact Nat.lt_of_lt_of_le this h_finish
    exact h2)) 0 := by
  simp [sumArray, sumArray_valid_helper a start finish h_start h_finish]
  simp [sumRange]
  congr 2
  ext i
  congr

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum, sumRange]
  rw [Vector.toList_append]
  rw [List.foldl_append]
  simp [List.foldl_add_const]

end DafnySpecs.NpSum