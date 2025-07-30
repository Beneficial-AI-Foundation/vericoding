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

/- LLM HELPER -/
lemma prodArray_zero_n {n : Nat} (a : Vector Int n) :
  prodArray a 0 n = a.toList.foldl (· * ·) 1 := by
  simp [prodArray]
  cases' n with n
  · simp
  · simp [List.range_succ]
    induction n with
    | zero => simp [Vector.toList]
    | succ n ih => 
      simp [List.range_succ, List.foldl_cons]
      sorry

/- LLM HELPER -/
lemma vector_get_eq {n : Nat} (a : Vector Int n) (i : Nat) (h : i < n) :
  a[i]! = a[i] := by
  simp [Vector.get]

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  simp [prod]
  apply prodArray_zero_n

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]!) 1 := by
  simp [prodArray]
  cases' Nat.eq_or_lt_of_le h_start with h h
  · simp [h]
  · simp [Nat.not_le.mpr h]

/- LLM HELPER -/
lemma prod_append_aux {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  (a ++ b).toList = a.toList ++ b.toList := by
  simp [Vector.append_def]

/- LLM HELPER -/
lemma foldl_append (l1 l2 : List Int) (init : Int) :
  (l1 ++ l2).foldl (· * ·) init = l2.foldl (· * ·) (l1.foldl (· * ·) init) := by
  simp [List.foldl_append]

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  simp [prod, prod_append_aux]
  rw [foldl_append]
  simp [mul_assoc]

/- LLM HELPER -/
lemma prod_zero_aux {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → ∃ x ∈ a.toList, x = 0 := by
  intro h
  use a[i]
  constructor
  · simp [Vector.toList_get]
  · exact h

/- LLM HELPER -/
lemma foldl_zero_mem (l : List Int) : 0 ∈ l → l.foldl (· * ·) 1 = 0 := by
  intro h
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.foldl_cons]
    cases' h with h h
    · simp [h]
    · simp [ih h]

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h
  simp [prod]
  apply foldl_zero_mem
  exact prod_zero_aux a i h

end DafnySpecs.NpProd