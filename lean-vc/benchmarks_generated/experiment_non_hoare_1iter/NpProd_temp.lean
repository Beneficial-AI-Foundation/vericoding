/-
# NumPy Product Specification

Port of np_prod.dfy to Lean 4
-/

namespace DafnySpecs.NpProd

/-- Product of all elements in a vector -/
def prod {n : Nat} (a : Vector Int n) : Int := 
  a.toList.foldl (· * ·) 1

/-- Helper function: product of elements from start to end (exclusive) -/
def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≥ finish then 1
  else (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]) 1

-- LLM HELPER
lemma prodArray_valid_index {n : Nat} (a : Vector Int n) (start finish : Nat) (i : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) (h_i : i < finish - start) :
  start + i < n := by
  have h1 : i < finish - start := h_i
  have h2 : start + i < start + (finish - start) := by
    rw [Nat.add_comm start]
    exact Nat.add_lt_add_right h1 start
  have h3 : start + (finish - start) = finish := by
    rw [Nat.add_comm]
    exact Nat.add_sub_cancel' h_start
  rw [h3] at h2
  exact Nat.lt_of_lt_of_le h2 h_finish

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  unfold prod prodArray
  simp only [Nat.zero_le, not_le_zero']
  congr 1
  ext i
  simp only [Nat.zero_add]
  rfl

-- LLM HELPER
lemma list_range_foldl_eq {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(prodArray_valid_index a start finish i h_start h_finish (by assumption))) 1 = 
  (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]) 1 := by
  congr 2
  ext acc i
  congr 2
  rfl

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(prodArray_valid_index a start finish i h_start h_finish (by assumption))) 1 := by
  unfold prodArray
  simp only [h_start, not_le]
  rw [list_range_foldl_eq]

-- LLM HELPER
lemma vector_append_toList {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  (a ++ b).toList = a.toList ++ b.toList := by
  rfl

-- LLM HELPER
lemma list_foldl_append (l1 l2 : List Int) :
  (l1 ++ l2).foldl (· * ·) 1 = l1.foldl (· * ·) 1 * l2.foldl (· * ·) 1 := by
  induction l1 generalizing l2 with
  | nil => simp [List.foldl]
  | cons h t ih => 
    simp [List.foldl]
    rw [ih]
    ring

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  unfold prod
  rw [vector_append_toList]
  exact list_foldl_append a.toList b.toList

-- LLM HELPER
lemma list_foldl_zero_mem (l : List Int) (h : 0 ∈ l) :
  l.foldl (· * ·) 1 = 0 := by
  induction l with
  | nil => contradiction
  | cons h t ih =>
    simp [List.foldl]
    cases' h with
    | inl h_eq => 
      rw [h_eq]
      simp [List.foldl_const]
    | inr h_mem => 
      rw [ih h_mem]
      simp

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h
  unfold prod
  apply list_foldl_zero_mem
  rw [Vector.mem_toList]
  use i
  exact h

end DafnySpecs.NpProd