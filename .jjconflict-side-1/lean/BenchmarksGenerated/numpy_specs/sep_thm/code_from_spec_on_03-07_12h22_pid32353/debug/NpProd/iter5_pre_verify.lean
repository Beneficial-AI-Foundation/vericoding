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
lemma vector_get_bound {n : Nat} (a : Vector Int n) (i : Nat) (hi : i < n) :
  a[i]! = a[i]'hi := by
  rfl

/- LLM HELPER -/
lemma prodArray_empty {n : Nat} (a : Vector Int n) (start : Nat) :
  prodArray a start start = 1 := by
  simp [prodArray]

/- LLM HELPER -/
lemma prodArray_bounds {n : Nat} (a : Vector Int n) (start finish : Nat) (h : start ≥ finish) :
  prodArray a start finish = 1 := by
  simp [prodArray, h]

/- LLM HELPER -/
lemma list_range_foldl_eq {n : Nat} (a : Vector Int n) (start : Nat) (len : Nat) (h : start + len ≤ n) :
  (List.range len).foldl (fun acc i => acc * a[start + i]!) 1 = 
  (List.range len).foldl (fun acc i => acc * a[start + i]'(by omega)) 1 := by
  congr 1
  ext acc i
  congr 1
  simp [vector_get_bound]

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  simp [prod, prodArray]
  if h : 0 ≥ n then
    have : n = 0 := by omega
    simp [this]
    cases' a with val prop
    simp [Vector.toList]
    cases' val with
    | nil => simp
    | cons h t => simp at prop
  else
    simp [h]
    have h_eq : n - 0 = n := by omega
    rw [h_eq]
    congr 1
    ext acc i
    congr 1
    rfl

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(by 
    have : i < finish - start := by 
      simp [List.mem_range]
      sorry
    have : start + i < finish := by omega
    have : start + i < n := by omega
    exact this)) 1 := by
  simp [prodArray]
  if h : start ≥ finish then
    have : finish - start = 0 := by omega
    simp [h, this]
  else
    simp [h]
    apply list_range_foldl_eq
    omega

/- LLM HELPER -/
lemma vector_toList_append {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  (a ++ b).toList = a.toList ++ b.toList := by
  rfl

/- LLM HELPER -/
lemma list_foldl_append (l1 l2 : List Int) :
  (l1 ++ l2).foldl (· * ·) 1 = l1.foldl (· * ·) 1 * l2.foldl (· * ·) 1 := by
  induction l1 with
  | nil => simp
  | cons h t ih => 
    simp [List.foldl_cons]
    rw [ih]
    ring

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  simp [prod]
  rw [vector_toList_append, list_foldl_append]

/- LLM HELPER -/
lemma list_foldl_zero {l : List Int} (h : 0 ∈ l) :
  l.foldl (· * ·) 1 = 0 := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.foldl_cons]
    cases' h with h h
    · simp [h]
    · rw [ih h]
      ring

/- LLM HELPER -/
lemma vector_mem_toList {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] ∈ a.toList := by
  simp [Vector.mem_toList_iff]
  use i
  rfl

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h
  simp [prod]
  apply list_foldl_zero
  rw [←h]
  exact vector_mem_toList a i

end DafnySpecs.NpProd