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

-- LLM HELPER
lemma vector_get_valid {n : Nat} (a : Vector Int n) (i : Nat) (h : i < n) :
  a[i] = a.get ⟨i, h⟩ := rfl

-- LLM HELPER
lemma sumArray_empty {n : Nat} (a : Vector Int n) (start : Nat) :
  sumArray a start start = 0 := by
  simp [sumArray]

-- LLM HELPER
lemma sumArray_recursive {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start < finish) (h_finish : finish ≤ n) :
  sumArray a start finish = a[start] + sumArray a (start + 1) finish := by
  simp [sumArray]
  rw [if_neg (not_le_of_lt h_start)]
  sorry

-- LLM HELPER
lemma list_sum_eq_foldr (l : List Int) :
  l.sum = l.foldr (· + ·) 0 := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.sum_cons, ih]

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  cases' n with n
  · simp
  · simp [Nat.succ_sub_zero]
    sorry

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => 
    if h : start + i < n then acc + a[start + i] else acc + 0) 0 := by
  simp [sumArray]
  rw [if_neg (not_lt_of_le h_start)]
  congr
  ext acc i
  simp
  cases' h : start + i < n with
  · rfl
  · simp [if_pos h]

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum]
  rw [Vector.toList_append]
  exact List.sum_append _ _

end DafnySpecs.NpSum