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
theorem Vector.get_append_left {α : Type*} {m n : Nat} (a : Vector α m) (b : Vector α n) (i : Fin m) :
  (a ++ b)[i.castAdd n] = a[i] := by
  simp [Vector.get_append_left]

/- LLM HELPER -/
theorem Vector.get_append_right {α : Type*} {m n : Nat} (a : Vector α m) (b : Vector α n) (i : Fin n) :
  (a ++ b)[i.natAdd m] = b[i] := by
  simp [Vector.get_append_right]

/- LLM HELPER -/
theorem List.foldl_append {α β : Type*} (f : β → α → β) (b : β) (l₁ l₂ : List α) :
  List.foldl f b (l₁ ++ l₂) = List.foldl f (List.foldl f b l₁) l₂ := by
  induction l₁ generalizing b with
  | nil => simp
  | cons h t ih => simp [List.foldl_cons, ih]

/- LLM HELPER -/
theorem Vector.toList_append {α : Type*} {m n : Nat} (a : Vector α m) (b : Vector α n) :
  (a ++ b).toList = a.toList ++ b.toList := by
  simp [Vector.toList_append]

/- LLM HELPER -/
theorem prodArray_zero_n {n : Nat} (a : Vector Int n) :
  prodArray a 0 n = a.toList.foldl (· * ·) 1 := by
  simp [prodArray]
  if h : 0 ≥ n then
    simp [h]
    have : n = 0 := Nat.eq_zero_of_le_zero h
    subst this
    simp [Vector.toList_nil]
  else
    simp [h]
    congr 1
    ext i
    simp [Nat.add_zero]

/- LLM HELPER -/
theorem List.mem_of_mem_foldl {α β : Type*} (f : β → α → β) (b : β) (l : List α) (x : α) :
  x ∈ l → ∃ b', f b' x = 0 → List.foldl f b l = 0 := by
  intro h
  induction l generalizing b with
  | nil => simp at h
  | cons h t ih => 
    simp at h
    cases h with
    | inl h => 
      subst h
      use b
      intro hf
      simp [List.foldl_cons, hf]
      induction t generalizing (f b x) with
      | nil => simp
      | cons h' t' ih' => 
        simp [List.foldl_cons]
        apply ih'
    | inr h => 
      have ⟨b', hb'⟩ := ih h
      use b'
      intro hf
      simp [List.foldl_cons]
      exact hb' hf

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  simp [prod]
  exact (prodArray_zero_n a).symm

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]!) 1 := by
  simp [prodArray]
  if h : start ≥ finish then
    have : start = finish := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt (not_lt.mp (not_not.mp (Nat.not_lt.mp h)))) (Nat.lt_succ_of_le h_start)
    simp [this, Nat.sub_self]
  else
    simp [h]
    rfl

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  simp [prod]
  rw [Vector.toList_append]
  rw [List.foldl_append]
  have : List.foldl (fun x1 x2 => x1 * x2) (List.foldl (fun x1 x2 => x1 * x2) 1 a.toList) b.toList = 
         List.foldl (fun x1 x2 => x1 * x2) 1 a.toList * List.foldl (fun x1 x2 => x1 * x2) 1 b.toList := by
    induction b.toList generalizing (List.foldl (fun x1 x2 => x1 * x2) 1 a.toList) with
    | nil => simp
    | cons h t ih => simp [List.foldl_cons, mul_assoc, ih]
  exact this

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h
  simp [prod]
  have : a[i] ∈ a.toList := by
    simp [Vector.toList_getElem]
    exact List.mem_ofFn_self i
  rw [← h] at this
  induction a.toList generalizing (1 : Int) with
  | nil => simp at this
  | cons h t ih => 
    simp at this
    cases this with
    | inl h_eq => 
      subst h_eq
      simp [List.foldl_cons, zero_mul]
      induction t generalizing (0 : Int) with
      | nil => simp
      | cons h' t' ih' => simp [List.foldl_cons, zero_mul, ih']
    | inr h_mem => 
      simp [List.foldl_cons]
      exact ih h_mem

end DafnySpecs.NpProd