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
  else List.foldl (fun acc i => 
    if h : start + i < n then acc + a[start + i] else acc) 0 (List.range (finish - start))

-- LLM HELPER
lemma sumArray_range_eq {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (a.toList.drop start).take (finish - start) |>.sum := by
  unfold sumArray
  simp [h_start]
  induction finish - start generalizing start with
  | zero => 
    simp [List.range_zero, List.foldl_nil]
    rfl
  | succ k ih =>
    have h_pos : 0 < finish - start := Nat.zero_lt_succ k
    have h_start_lt : start < finish := Nat.lt_of_le_of_lt h_start (Nat.lt_of_sub_pos h_pos)
    have h_start_lt_n : start < n := Nat.lt_of_lt_of_le h_start_lt h_finish
    simp [List.range_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← ih]
    · simp [sumArray, Nat.succ_sub_succ_eq_sub, Nat.zero_sub]
      congr 1
      · exact Nat.le_of_lt h_start_lt
      · exact h_finish
    · exact Nat.le_of_lt h_start_lt
    · exact h_finish

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  unfold sum sumArray
  simp
  induction n with
  | zero => simp [Vector.toList_nil]
  | succ k ih =>
    simp [List.range_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    congr 1
    · rw [← ih]
      rfl
    · simp

-- LLM HELPER
lemma range_mem_lt {k i : Nat} (h : i ∈ List.range k) : i < k := by
  exact List.mem_range.mp h

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = List.foldl (fun acc i => acc + a[start + i]'(Nat.add_lt_of_lt_sub (range_mem_lt (by assumption : i ∈ List.range (finish - start))) h_finish)) 0 (List.range (finish - start)) := by
  unfold sumArray
  simp [h_start]
  congr 2
  ext acc i
  simp
  by_cases h : start + i < n
  · simp [h]
  · simp [h]
    exfalso
    have : i < finish - start := by
      apply range_mem_lt
      assumption
    have : start + i < finish := Nat.add_lt_of_lt_sub' this
    have : start + i < n := Nat.lt_of_lt_of_le this h_finish
    exact h this

-- LLM HELPER
lemma List.sum_append {α : Type*} [Add α] [Zero α] (l₁ l₂ : List α) : 
  (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons h t ih => 
    simp [List.sum_cons, List.cons_append]
    rw [ih]
    ring

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  unfold sum
  rw [Vector.toList_append]
  rw [List.sum_append]

end DafnySpecs.NpSum