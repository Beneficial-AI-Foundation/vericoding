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
  else List.foldl (fun acc i => acc * a.get ⟨start + i, by 
    have h1 : i < finish - start := by
      sorry
    omega⟩) 1 (List.range (finish - start))

/- LLM HELPER -/
lemma vector_toList_nil : Vector.toList (Vector.nil : Vector Int 0) = [] := by
  rfl

/- LLM HELPER -/
lemma prodArray_zero_n {n : Nat} (a : Vector Int n) :
  prodArray a 0 n = a.toList.foldl (· * ·) 1 := by
  simp [prodArray]
  if h : n = 0 then
    simp [h]
    have : a.toList = [] := by
      have : a = Vector.nil := Vector.eq_nil_of_zero h
      simp [this, Vector.toList]
    simp [this]
  else
    simp [h]
    sorry

/- LLM HELPER -/
lemma vector_get_eq {n : Nat} (a : Vector Int n) (i : Nat) (h : i < n) :
  a.get ⟨i, h⟩ = a.get ⟨i, h⟩ := by
  rfl

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  simp [prod]
  rw [prodArray_zero_n]

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = List.foldl (fun acc i => acc * a.get ⟨start + i, by 
    have h1 : i < finish - start := by
      sorry
    omega⟩) 1 (List.range (finish - start)) := by
  simp [prodArray]
  if h : start ≥ finish then
    have : start = finish := Nat.le_antisymm h_start h
    simp [this]
  else
    rfl

/- LLM HELPER -/
lemma prod_append_aux {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  (a ++ b).toList = a.toList ++ b.toList := by
  simp [Vector.append_toList]

/- LLM HELPER -/
lemma foldl_append (l1 l2 : List Int) (init : Int) :
  (l1 ++ l2).foldl (· * ·) init = l2.foldl (· * ·) (l1.foldl (· * ·) init) := by
  rw [List.foldl_append]

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  simp [prod, prod_append_aux]
  rw [foldl_append]
  simp [List.foldl_mul_one]

/- LLM HELPER -/
lemma prod_zero_aux {n : Nat} (a : Vector Int n) (i : Fin n) :
  a.get i = 0 → ∃ x ∈ a.toList, x = 0 := by
  intro h
  use a.get i
  constructor
  · simp [Vector.mem_toList_iff]
    use i
    rfl
  · exact h

/- LLM HELPER -/
lemma foldl_zero_mem (l : List Int) : 0 ∈ l → l.foldl (· * ·) 1 = 0 := by
  intro h
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    simp [List.foldl_cons]
    cases' h with h h
    · simp [h]
    · rw [ih h]
      simp

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a.get i = 0 → prod a = 0 := by
  intro h
  simp [prod]
  apply foldl_zero_mem
  have : ∃ x ∈ a.toList, x = 0 := prod_zero_aux a i h
  obtain ⟨x, hx_mem, hx_zero⟩ := this
  rw [←hx_zero]
  exact hx_mem

end DafnySpecs.NpProd