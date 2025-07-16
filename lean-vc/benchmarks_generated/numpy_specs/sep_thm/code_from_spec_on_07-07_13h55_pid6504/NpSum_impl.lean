/-
# NumPy Sum Specification

Port of np_sum.dfy to Lean 4
-/

namespace DafnySpecs.NpSum

-- LLM HELPER
/-- Helper function: sum of elements from start to end (exclusive) -/
def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if h : start < finish ∧ finish ≤ n then
    (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by
      have h1 : i < finish - start := by
        exact List.mem_range.1 this
      have h2 : finish ≤ n := h.2
      omega)) 0
  else 0

/-- Sum of all elements in a vector -/
def sum {n : Nat} (a : Vector Int n) : Int := sumArray a 0 n

-- LLM HELPER
lemma sumArray_empty {n : Nat} (a : Vector Int n) (start : Nat) :
  sumArray a start start = 0 := by
  simp [sumArray]

-- LLM HELPER
lemma sumArray_out_of_bounds {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h : ¬(start < finish ∧ finish ≤ n)) :
  sumArray a start finish = 0 := by
  simp [sumArray, h]

/-- Specification: sum returns the sum of all elements -/
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  unfold sum
  rfl

/-- Specification: sumArray with valid bounds computes partial sum -/
theorem sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by
    have h1 : i < finish - start := by
      exact List.mem_range.1 this
    omega)) 0 := by
  by_cases h : start < finish
  · simp [sumArray, h, h_finish]
  · have : start = finish := by omega
    simp [this]
    rw [sumArray_empty]
    simp [List.range]

-- LLM HELPER
lemma sumArray_rec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start < finish) (h_finish : finish ≤ n) :
  sumArray a start finish = a[start]'(by omega) + sumArray a (start + 1) finish := by
  simp [sumArray, h_start, h_finish]
  have h_range : List.range (finish - start) = 0 :: List.range (finish - start - 1) := by
    have : finish - start > 0 := by omega
    exact List.range_succ_eq_map (finish - start - 1)
  simp [h_range]
  congr 1
  · simp
  · simp [List.foldl_cons]

-- LLM HELPER
lemma sumArray_split {m n : Nat} (a : Vector Int m) (b : Vector Int n) (start mid finish : Nat) 
  (h1 : start ≤ mid) (h2 : mid ≤ finish) (h3 : finish ≤ m + n) :
  sumArray (a ++ b) start finish = sumArray (a ++ b) start mid + sumArray (a ++ b) mid finish := by
  induction' finish using Nat.strong_induction_on with finish ih
  by_cases h : start < finish
  · by_cases h_mid : start < mid
    · by_cases h_mid_fin : mid < finish
      · simp [sumArray, h, h_mid, h_mid_fin]
        ring
      · have : mid = finish := by omega
        simp [this, sumArray_empty]
    · have : start = mid := by omega
      simp [this, sumArray_empty]
  · have : start = finish := by omega
    simp [this, sumArray_empty]

-- LLM HELPER
lemma sumArray_concat_left {m n : Nat} (a : Vector Int m) (b : Vector Int n) (start finish : Nat)
  (h1 : start ≤ finish) (h2 : finish ≤ m) :
  sumArray (a ++ b) start finish = sumArray a start finish := by
  by_cases h : start < finish ∧ finish ≤ m + n
  · simp [sumArray, h, h2]
    congr 2
    funext acc i
    congr 1
    simp [Vector.append_val]
    rfl
  · simp [sumArray, h]
    simp [sumArray, h2]

-- LLM HELPER  
lemma sumArray_concat_right {m n : Nat} (a : Vector Int m) (b : Vector Int n) (start finish : Nat)
  (h1 : m ≤ start) (h2 : start ≤ finish) (h3 : finish ≤ m + n) :
  sumArray (a ++ b) start finish = sumArray b (start - m) (finish - m) := by
  by_cases h : start < finish
  · simp [sumArray, h, h3]
    simp [sumArray, Nat.sub_lt_iff_lt_add h1, h2, h3]
    congr 2
    funext acc i
    congr 1
    simp [Vector.append_val]
    have : m ≤ start + i := by omega
    simp [this]
    congr 1
    omega
  · have : start = finish := by omega
    simp [this, sumArray_empty]

/-- Specification: sum is associative with concatenation -/
theorem sum_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum]
  have h1 : sumArray (a ++ b) 0 (m + n) = sumArray (a ++ b) 0 m + sumArray (a ++ b) m (m + n) := by
    apply sumArray_split
    · omega
    · omega
    · omega
  have h2 : sumArray (a ++ b) 0 m = sumArray a 0 m := by
    apply sumArray_concat_left
    · omega
    · omega
  have h3 : sumArray (a ++ b) m (m + n) = sumArray b 0 n := by
    rw [sumArray_concat_right]
    · simp
    · omega
    · omega
    · omega
  rw [h1, h2, h3]

end DafnySpecs.NpSum