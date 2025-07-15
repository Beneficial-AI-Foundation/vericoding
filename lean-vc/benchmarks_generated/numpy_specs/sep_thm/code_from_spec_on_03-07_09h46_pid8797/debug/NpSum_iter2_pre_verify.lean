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
        have : i ∈ List.range (n + 1) := by assumption
        rw [List.mem_range] at this
        exact h this
    rw [h_fold]
    rw [Vector.toList_sum_eq_foldl_range]

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by 
    have : i < finish - start := by assumption
    linarith)) 0 := by
  simp [sumArray]
  by_cases h : start ≥ finish
  · have : start = finish := by linarith
    simp [this, Nat.sub_self]
  · simp [h]
    congr 1
    ext acc i
    simp
    have h_bound : start + i < n := by
      have : i ∈ List.range (finish - start) := by assumption
      rw [List.mem_range] at this
      linarith
    simp [h_bound]
    rfl

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum]
  rw [Vector.toList_append]
  rw [List.sum_append]

/- LLM HELPER -/
theorem Vector.toList_sum_eq_foldl_range {n : Nat} (a : Vector Int n) :
  a.toList.sum = (List.range n).foldl (fun acc i => acc + a[i]'(by assumption)) 0 := by
  induction n with
  | zero => 
    simp [Vector.toList_eq_nil_iff]
    simp [List.range_zero, List.foldl_nil]
  | succ n ih =>
    simp [Vector.toList]
    rw [List.sum_cons]
    have : (List.range (n + 1)).foldl (fun acc i => acc + a[i]'(by assumption)) 0 = 
           a[0] + (List.range n).foldl (fun acc i => acc + a[i+1]'(by assumption)) 0 := by
      simp [List.range_succ, List.foldl_cons, List.foldl_map]
      congr 1
      ext acc i
      simp
      rfl
    rw [this]
    simp [Vector.head_val]
    congr 1
    have : (List.range n).foldl (fun acc i => acc + a[i+1]'(by assumption)) 0 = 
           (List.range n).foldl (fun acc i => acc + (Vector.tail a)[i]'(by assumption)) 0 := by
      congr 1
      ext acc i
      simp [Vector.tail_val]
      rfl
    rw [this]
    rw [← ih]
    simp [Vector.tail_val]

end DafnySpecs.NpSum