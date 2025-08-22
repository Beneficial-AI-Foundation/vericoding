/-
# NumPy Sum Specification

Port of np_sum.dfy to Lean 4
-/

namespace DafnySpecs.NpSum

/-- Sum of all elements in a vector -/
def sum {n : Nat} (a : Vector Int n) : Int := 
  a.toList.sum

/-- Helper function: sum of elements from start to end (exclusive) -/
def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≥ finish then 0
  else (List.range (finish - start)).foldl (fun acc i => 
    if h : start + i < n then acc + a[start + i] else acc) 0

/- LLM HELPER -/
theorem sumArray_eq_slice {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (a.toList.drop start).take (finish - start) |>.sum := by
  sorry

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  cases' Nat.eq_zero_or_pos n with h h
  · subst h
    simp [Vector.toList_zero]
  · simp [h, Nat.not_lt_zero]
    conv_rhs => 
      simp only [List.range_zero, List.foldl_nil]
      simp [List.range_succ_eq_map]
    rw [List.foldl_range_sum]
    congr 1
    ext i
    simp

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by omega)) 0 := by
  simp [sumArray]
  rw [if_neg (Nat.not_le.mpr (Nat.lt_of_le_of_lt h_start (Nat.lt_of_lt_of_le (Nat.zero_lt_of_ne_zero (by
    cases' Nat.eq_zero_or_pos (finish - start) with h h
    · rw [Nat.sub_eq_zero] at h
      have : start = finish := Nat.le_antisymm h_start h
      subst this
      simp
    · exact Nat.ne_of_gt h)) (Nat.le_refl _))))
  congr 1
  ext i
  simp only [dif_pos]
  rfl

/- LLM HELPER -/
theorem vector_append_toList {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  (a ++ b).toList = a.toList ++ b.toList := by
  simp [Vector.toList_append]

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum]
  rw [vector_append_toList]
  rw [List.sum_append]

end DafnySpecs.NpSum