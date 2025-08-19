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
    a[start + i]))

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
  a.toList = List.map (fun i => a[i]) (List.range n) := by
  apply List.ext_get
  · simp [Vector.toList_length]
  · intro i h1 h2
    simp [List.get_map, List.get_range]
    simp [Vector.get_toList]

/-- LLM HELPER -/
lemma foldl_add_assoc (acc : Int) (l : List Int) :
  List.foldl (fun x1 x2 => x1 + x2) acc l = acc + List.foldl (fun x1 x2 => x1 + x2) 0 l := by
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
  if h : n = 0 then
    simp [h, Vector.toList_eq_nil_iff.mpr h]
  else
    rw [vector_toList_eq_map_range]
    simp [List.map_map]
    congr
    ext i
    simp

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => 
    acc + a[start + i]) 0 := by
  simp [sumArray]
  split
  · simp
  · simp [sumRange]
    rw [List.foldl_map]
    congr

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum, sumRange]
  rw [Vector.toList_append]
  rw [List.foldl_append]
  rw [foldl_add_assoc]

end DafnySpecs.NpSum