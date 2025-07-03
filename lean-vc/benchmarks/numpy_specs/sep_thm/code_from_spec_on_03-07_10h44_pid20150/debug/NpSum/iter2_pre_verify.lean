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
theorem list_sum_eq_foldl (l : List Int) : l.sum = List.foldl (· + ·) 0 l := by
  induction l with
  | nil => simp [List.sum]
  | cons h t ih => simp [List.sum, List.foldl, ih]

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  cases' n with n
  · simp [Vector.toList]
  · simp [Vector.toList]
    rw [list_sum_eq_foldl]
    simp [List.foldl]

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by linarith [h_start, h_finish])) 0 := by
  simp [sumArray]
  rw [if_neg (not_le.mpr (Nat.lt_of_le_of_ne h_start (fun h => by simp [h] at h_start)))]
  congr 1
  ext acc i
  simp
  have h : start + i < n := by linarith [h_start, h_finish]
  rw [dif_pos h]
  rfl

/- LLM HELPER -/
theorem list_sum_append (l1 l2 : List Int) : (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil => simp
  | cons h t ih => simp [List.sum, ih, add_assoc]

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum, Vector.toList_append, list_sum_append]

end DafnySpecs.NpSum