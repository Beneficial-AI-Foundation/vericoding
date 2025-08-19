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
  else sumRange ((List.range (finish - start)).map (fun i => a[start + i]))

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

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  cases' n with n
  · simp [sum, sumArray, sumRange, Vector.toList_nil]
  · simp [sum, sumArray, sumRange]
    congr 1
    have : a.toList = List.map (fun i => a[i]) (List.range (n + 1)) := by
      apply List.ext_get
      · simp
      · intro i h1 h2
        simp [List.get_map, List.get_range]

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]) 0 := by
  cases' Nat.eq_or_lt_of_le h_start with h h
  · rw [h]
    simp [sumArray]
  · simp [sumArray, sumArray_valid_helper a start finish h h_finish]
    simp [sumRange]

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum, sumRange]
  rw [Vector.toList_append]
  rw [List.foldl_append]

end DafnySpecs.NpSum