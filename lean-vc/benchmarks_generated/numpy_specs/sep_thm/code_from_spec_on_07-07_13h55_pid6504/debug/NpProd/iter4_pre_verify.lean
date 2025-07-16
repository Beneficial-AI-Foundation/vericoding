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
  simp [prodArray]
  split
  · simp
    split <;> simp
  · split
    · simp
    · simp
      induction (finish - start) with
      | zero => simp
      | succ k ih => simp [List.range, List.foldl]

-- LLM HELPER
lemma list_foldl_eq_prodArray {n : Nat} (a : Vector Int n) :
  a.toList.foldl (· * ·) 1 = prodArray a 0 n := by
  simp [prodArray]
  by_cases h : n = 0
  · simp [h]
    have : a.toList = [] := by
      simp [Vector.toList, h]
    simp [this, List.foldl]
  · simp [h]
    have : ¬(0 ≥ n) := by omega
    simp [this]
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
  · case isTrue h =>
    have : finish - start = 0 := by omega
    simp [this, List.range, List.foldl]
  · case isFalse h =>
    rfl

-- LLM HELPER
lemma List.foldl_mul_assoc (init : Int) (a b : List Int) :
  List.foldl (· * ·) (List.foldl (· * ·) init a) b = 
  List.foldl (· * ·) init a * List.foldl (· * ·) 1 b := by
  induction a generalizing init with
  | nil => simp [List.foldl]
  | cons head tail ih =>
    simp [List.foldl]
    rw [ih]
    ring

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  simp [prod]
  simp [Vector.toList_append]
  exact List.foldl_mul_assoc 1 a.toList b.toList

-- LLM HELPER
lemma List.mem_of_get {α : Type*} (l : List α) (i : Fin l.length) :
  l[i] ∈ l := by
  induction l with
  | nil => simp at i
  | cons head tail ih =>
    cases' i with val hval
    simp at hval
    cases val with
    | zero => simp [List.get]
    | succ k =>
      simp [List.get]
      apply List.mem_cons_of_mem
      have : k < tail.length := by simp at hval; exact Nat.lt_of_succ_lt_succ hval
      exact ih ⟨k, this⟩

-- LLM HELPER
lemma List.foldl_eq_zero_of_zero_mem (l : List Int) (h : 0 ∈ l) :
  List.foldl (· * ·) 1 l = 0 := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.foldl]
    cases h with
    | head => simp
    | tail h_tail =>
      have : List.foldl (· * ·) head tail = 0 := by
        induction tail generalizing head with
        | nil => simp at h_tail
        | cons t_head t_tail t_ih =>
          simp [List.foldl]
          cases h_tail with
          | head => simp
          | tail h_t_tail => exact t_ih h_t_tail
      simp [this]

-- LLM HELPER
lemma Vector.toList_get {n : Nat} (a : Vector Int n) (i : Fin n) :
  a.toList[i.val] = a[i] := by
  simp [Vector.toList]

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h
  simp [prod]
  have : a[i] ∈ a.toList := by
    have h_len : i.val < a.toList.length := by simp [Vector.length_toList]
    have : a.toList[i.val] = a[i] := Vector.toList_get a i
    rw [← this]
    exact List.mem_of_get a.toList ⟨i.val, h_len⟩
  rw [← h] at this
  exact List.foldl_eq_zero_of_zero_mem a.toList this

end DafnySpecs.NpProd