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
  | cons h t ih => 
    simp [List.sum, List.foldl]
    rw [← ih]
    simp [List.sum]
    ring

/- LLM HELPER -/
theorem vector_zero_toList_empty {n : Nat} (a : Vector Int n) (h : n = 0) : a.toList = [] := by
  have : a.toList.length = 0 := by simp [Vector.toList_length, h]
  exact List.eq_nil_of_length_eq_zero this

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  by_cases h : n = 0
  · simp [h]
    rw [vector_zero_toList_empty a h]
    simp [List.sum]
  · simp [h]
    rw [list_sum_eq_foldl]
    congr 1
    funext acc i
    simp
    have h_bound : 0 + i < n := by
      have : i < List.length (List.range (n - 0)) := by simp
      simp at this
      exact this
    rw [dif_pos h_bound]
    simp [Nat.zero_add]

/- LLM HELPER -/
theorem range_add_bound (start finish : Nat) (i : Nat) (h_start : start ≤ finish) (h_finish : finish ≤ n) 
  (h_in_range : i ∈ List.range (finish - start)) : start + i < n := by
  simp [List.mem_range] at h_in_range
  omega

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by omega)) 0 := by
  simp [sumArray]
  split_ifs with h
  · simp
  · congr 1
    funext acc i
    simp
    have h_bound : start + i < n := by omega
    rw [dif_pos h_bound]
    rfl

/- LLM HELPER -/
theorem list_sum_append (l1 l2 : List Int) : (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil => simp
  | cons h t ih => 
    simp [List.sum, ih]
    ring

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum, Vector.toList_append, list_sum_append]

end DafnySpecs.NpSum