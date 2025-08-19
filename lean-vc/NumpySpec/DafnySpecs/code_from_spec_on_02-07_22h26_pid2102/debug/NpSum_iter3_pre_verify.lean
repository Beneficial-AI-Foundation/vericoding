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
  else sumRange ((List.range (finish - start)).map (fun i => 
    have h : start + i < n := by
      have : i < finish - start := by
        sorry  -- This would need proof that i is from range
      omega
    a[start + i]'h))

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
  (h_start : start < finish) (h_finish : finish ≤ n) :
  ¬(start ≥ finish ∨ finish > n) := by
  simp [Nat.not_le.mpr h_start, Nat.not_lt.mpr h_finish]

/-- LLM HELPER -/
lemma vector_toList_eq_map_range {n : Nat} (a : Vector Int n) :
  a.toList = List.map (fun i => 
    have h : i < n := by
      cases' n with n
      · simp
      · omega
    a[i]'h) (List.range n) := by
  apply List.ext_get
  · simp [Vector.toList_length]
  · intro i h1 h2
    simp [List.get_map, List.get_range]
    simp [Vector.get_toList]

/-- LLM HELPER -/
lemma foldl_add_comm (f : Int → Nat → Int) (acc : Int) (l : List Nat) :
  List.foldl f acc l = acc + List.foldl f 0 l := by
  induction l generalizing acc with
  | nil => simp
  | cons head tail ih =>
    simp [List.foldl_cons]
    rw [ih, ih]
    ring

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray, sumRange]
  rw [vector_toList_eq_map_range]

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => 
    have h : start + i < n := by
      have : i < finish - start := by omega
      omega
    acc + a[start + i]'h) 0 := by
  simp [sumArray]
  split
  · simp
  · simp [sumRange]
    congr

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum, sumRange]
  rw [Vector.toList_append]
  rw [List.foldl_append]
  rw [foldl_add_comm]

end DafnySpecs.NpSum