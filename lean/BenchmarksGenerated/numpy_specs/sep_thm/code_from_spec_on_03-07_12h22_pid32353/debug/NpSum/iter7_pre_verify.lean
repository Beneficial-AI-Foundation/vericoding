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
  sumArray a start finish = (a.toList.drop start |>.take (finish - start)).sum := by
  simp [sumArray]
  cases' Nat.le_iff_eq_or_lt.mp h_start with h h
  · subst h
    simp
  · simp [Nat.not_le.mpr h]
    induction' (finish - start) with k ih generalizing start
    · simp
    · simp [List.range_succ, List.foldl_cons]
      rw [List.sum_cons]
      simp only [List.take_succ, List.drop_succ_cons]
      have h_bound : start + 0 < n := by
        have : start < finish := Nat.lt_of_le_of_ne h_start (Ne.symm (Nat.ne_of_gt h))
        omega
      simp [h_bound]
      congr 1
      exact ih

/- LLM HELPER -/
theorem List.foldl_range_sum {n : Nat} (a : Vector Int n) :
  List.foldl (fun acc i => if h : i < n then acc + a[i] else acc) 0 (List.range n) = 
  List.foldl (fun acc i => acc + a[i]) 0 (List.range n) := by
  induction' n with k ih
  · simp
  · simp [List.range_succ, List.foldl_append, List.foldl_cons]
    have h_bound : k < k + 1 := Nat.lt_succ_self k
    simp [h_bound]
    rw [ih]

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  cases' Nat.eq_zero_or_pos n with h h
  · subst h
    simp
  · simp [Nat.not_le.mpr h]
    rw [List.foldl_range_sum]
    rw [← List.sum_eq_foldl_add]
    congr 1
    ext i
    simp [Vector.get_toList]

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]) 0 := by
  simp [sumArray]
  cases' Nat.le_iff_eq_or_lt.mp h_start with h h
  · subst h
    simp
  · simp [Nat.not_le.mpr h]
    congr 1
    ext acc i
    simp only [dif_pos]
    have h_bound : start + i < n := by
      have : i < finish - start := by
        simp [List.mem_range]
        omega
      omega
    simp [h_bound]

/- LLM HELPER -/
theorem vector_append_toList {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  (a ++ b).toList = a.toList ++ b.toList := by
  simp [Vector.toList_append]

/- LLM HELPER -/
theorem List.sum_append (l₁ l₂ : List Int) :
  (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction' l₁ with h t ih
  · simp
  · simp [List.sum_cons, ih, add_assoc]

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum]
  rw [vector_append_toList]
  rw [List.sum_append]

end DafnySpecs.NpSum