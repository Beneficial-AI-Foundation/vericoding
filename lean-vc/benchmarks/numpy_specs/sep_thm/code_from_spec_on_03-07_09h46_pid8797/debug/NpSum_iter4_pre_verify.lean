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
theorem Vector.toList_sum_eq_foldl_range {n : Nat} (a : Vector Int n) :
  a.toList.sum = (List.range n).foldl (fun acc i => acc + a[i]) 0 := by
  induction n with
  | zero => 
    simp [Vector.toList_eq_nil_iff]
    simp [List.range_zero, List.foldl_nil]
  | succ n ih =>
    simp [Vector.toList]
    rw [List.sum_eq_foldl]
    congr

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  cases' n with n
  · simp [Vector.toList_eq_nil_iff]
  · simp [Nat.succ_sub_zero]
    have h_fold : (List.range (n + 1)).foldl (fun acc i => 
      if h : 0 + i < n + 1 then acc + a[0 + i] else acc) 0 = 
      (List.range (n + 1)).foldl (fun acc i => acc + a[i]) 0 := by
      congr 1
      ext acc i
      simp [Nat.zero_add]
      split_ifs with h
      · rfl
      · exfalso
        have : i < n + 1 := by
          simp [List.mem_range] at *
          assumption
        exact h this
    rw [h_fold]
    rw [Vector.toList_sum_eq_foldl_range]

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by 
    have : i < finish - start := by assumption
    linarith [h_start, h_finish])) 0 := by
  simp [sumArray]
  by_cases h : start ≥ finish
  · have : start = finish := by linarith
    simp [this, Nat.sub_self]
  · simp [h]
    congr 1
    ext acc i
    simp
    have h_bound : start + i < n := by
      linarith [h_start, h_finish]
    simp [h_bound]
    rfl

/- LLM HELPER -/
theorem List.sum_append {α : Type*} [Add α] [Zero α] (l1 l2 : List α) : 
  (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil => simp
  | cons a l1 ih => 
    simp [List.sum_cons]
    rw [ih]
    rw [add_assoc]

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum]
  rw [Vector.toList_append]
  rw [List.sum_append]

end DafnySpecs.NpSum