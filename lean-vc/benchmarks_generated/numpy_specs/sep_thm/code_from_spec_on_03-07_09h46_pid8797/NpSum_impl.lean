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
theorem List.sum_eq_foldl_add_zero (l : List Int) :
  l.sum = l.foldl (· + ·) 0 := by
  induction l with
  | nil => simp
  | cons a l ih => 
    simp [List.sum_cons, List.foldl_cons]
    rw [ih]

/- LLM HELPER -/
theorem Vector.toList_sum_eq_foldl_range {n : Nat} (a : Vector Int n) :
  a.toList.sum = if n = 0 then 0 else (List.range n).foldl (fun acc i => 
    if h : i < n then acc + a[i] else acc) 0 := by
  cases' n with n
  · simp [Vector.toList_eq_nil_iff]
  · simp
    rw [List.sum_eq_foldl_add_zero]
    congr 1
    ext acc i
    simp

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  cases' n with n
  · simp [Vector.toList_eq_nil_iff]
  · simp [Nat.succ_sub_zero]
    rw [Vector.toList_sum_eq_foldl_range]
    simp
    congr 1
    ext acc i
    simp [Nat.zero_add]

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => 
    let h_bound : i < finish - start := by 
      simp [List.mem_range]
    acc + a[start + i]'(by linarith [h_start, h_finish, h_bound])) 0 := by
  simp [sumArray]
  by_cases h : start ≥ finish
  · have : start = finish := by linarith
    simp [this, Nat.sub_self]
  · simp [h]
    congr 1
    ext acc i
    simp
    split_ifs with h_bound
    · rfl
    · simp

/- LLM HELPER -/
theorem List.sum_append (l1 l2 : List Int) : 
  (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil => simp
  | cons a l1 ih => 
    simp [List.sum_cons]
    rw [ih]
    rw [Int.add_assoc]

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum]
  rw [Vector.toList_append]
  rw [List.sum_append]

end DafnySpecs.NpSum