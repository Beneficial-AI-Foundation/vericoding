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
  else (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]!) 1

-- LLM HELPER
lemma prodArray_empty {n : Nat} (a : Vector Int n) (start : Nat) :
  prodArray a start start = 1 := by
  simp [prodArray]

-- LLM HELPER
lemma prodArray_single {n : Nat} (a : Vector Int n) (i : Nat) (h : i < n) :
  prodArray a i (i + 1) = a[i] := by
  simp [prodArray]
  simp [List.range, List.foldl]
  congr 1
  simp [Vector.get_eq_getElem]

-- LLM HELPER
lemma prodArray_split {n : Nat} (a : Vector Int n) (start mid finish : Nat) 
  (h1 : start ≤ mid) (h2 : mid ≤ finish) (h3 : finish ≤ n) :
  prodArray a start finish = prodArray a start mid * prodArray a mid finish := by
  sorry

-- LLM HELPER
lemma list_foldl_eq_prodArray {n : Nat} (a : Vector Int n) :
  a.toList.foldl (· * ·) 1 = prodArray a 0 n := by
  simp [prodArray]
  have h : n = a.toList.length := by simp [Vector.length_toList]
  rw [← h]
  induction a.toList with
  | nil => simp [List.foldl]
  | cons head tail ih =>
    simp [List.foldl]
    sorry

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  simp [prod]
  exact list_foldl_eq_prodArray a

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]!) 1 := by
  simp [prodArray]
  split
  · case inl h =>
    have : finish - start = 0 := by omega
    simp [this, List.range, List.foldl]
  · case inr h =>
    rfl

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  simp [prod]
  simp [Vector.toList_append]
  induction a.toList with
  | nil => simp [List.foldl]
  | cons head tail ih =>
    simp [List.foldl]
    rw [← ih]
    ring

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h
  simp [prod]
  have : a[i] ∈ a.toList := by
    simp [Vector.toList, List.get_mem]
  induction a.toList with
  | nil => simp at this
  | cons head tail ih =>
    simp [List.foldl]
    cases' this with h1 h2
    · simp [h1, h]
    · apply ih h2

end DafnySpecs.NpProd