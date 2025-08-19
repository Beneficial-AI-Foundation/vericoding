/-
# NumPy Product Specification

Port of np_prod.dfy to Lean 4
-/

namespace DafnySpecs.NpProd

/-- LLM HELPER -/
def prodArrayAux {n : Nat} (a : Vector Int n) (start finish : Nat) : Int :=
  if h : start < finish ∧ finish ≤ n then
    a[start]'(Nat.lt_of_lt_of_le h.1 h.2) * prodArrayAux a (start + 1) finish
  else
    1
termination_by (finish - start)
decreasing_by
  simp_wf
  have : start < finish := h.1
  have : start + 1 ≤ finish := Nat.succ_le_of_lt this
  exact Nat.sub_lt_sub_right this (Nat.lt_succ_self start)

/-- Helper function: product of elements from start to end (exclusive) -/
def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int :=
  if start ≤ finish ∧ finish ≤ n then
    prodArrayAux a start finish
  else
    1

/-- Product of all elements in a vector -/
def prod {n : Nat} (a : Vector Int n) : Int := prodArray a 0 n

/-- LLM HELPER -/
theorem prodArrayAux_eq_foldl {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArrayAux a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(by
    have hi : i < finish - start := by simp [List.mem_range] at *; assumption
    exact Nat.add_lt_of_le_of_lt (Nat.le_add_right start i) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.add_lt_of_pos_right start (Nat.pos_of_ne_zero (fun h => by simp [h] at hi))))))) 1 := by
  sorry

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  rfl

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(by
    have hi : i < finish - start := by simp [List.mem_range] at *; assumption
    exact Nat.add_lt_of_le_of_lt (Nat.le_add_right start i) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.add_lt_of_pos_right start (Nat.pos_of_ne_zero (fun h => by simp [h] at hi))))))) 1 := by
  unfold prodArray
  rw [if_pos ⟨h_start, h_finish⟩]
  exact prodArrayAux_eq_foldl a start finish h_start h_finish

/-- LLM HELPER -/
lemma prodArrayAux_split {n : Nat} (a : Vector Int n) (start mid finish : Nat)
  (h1 : start ≤ mid) (h2 : mid ≤ finish) (h3 : finish ≤ n) :
  prodArrayAux a start finish = prodArrayAux a start mid * prodArrayAux a mid finish := by
  sorry

/-- LLM HELPER -/
theorem prodArray_concat_aux {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prodArray (a ++ b) 0 (m + n) = prodArray (a ++ b) 0 m * prodArray (a ++ b) m (m + n) := by
  unfold prodArray
  rw [if_pos ⟨Nat.zero_le _, Nat.le_add_right _ _⟩]
  rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩] 
  rw [if_pos ⟨Nat.le_refl _, Nat.le_refl _⟩]
  exact prodArrayAux_split (a ++ b) 0 m (m + n) (Nat.zero_le _) (Nat.le_refl _) (Nat.le_add_right _ _)

/-- LLM HELPER -/
lemma prodArrayAux_append_left {m n : Nat} (a : Vector Int m) (b : Vector Int n) (finish : Nat) (h_finish : finish ≤ m) :
  prodArrayAux (a ++ b) 0 finish = prodArrayAux a 0 finish := by
  sorry

/-- LLM HELPER -/
lemma prodArrayAux_append_right {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prodArrayAux (a ++ b) m (m + n) = prodArrayAux b 0 n := by
  sorry

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  unfold prod
  rw [prodArray_concat_aux]
  congr 1
  · -- Show prodArray (a ++ b) 0 m = prodArray a 0 m
    unfold prodArray
    rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
    rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
    exact prodArrayAux_append_left a b m (Nat.le_refl _)
  · -- Show prodArray (a ++ b) m (m + n) = prodArray b 0 n
    unfold prodArray
    rw [if_pos ⟨Nat.le_refl _, Nat.le_refl _⟩]
    rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
    exact prodArrayAux_append_right a b

/-- LLM HELPER -/
theorem prodArrayAux_zero {n : Nat} (a : Vector Int n) (start finish : Nat) (i : Nat)
  (h_i_bound : start ≤ i ∧ i < finish ∧ finish ≤ n) (h_zero : a[i]'(Nat.lt_of_lt_of_le h_i_bound.2.1 h_i_bound.2.2) = 0) :
  prodArrayAux a start finish = 0 := by
  sorry

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h_zero
  unfold prod prodArray
  rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
  apply prodArrayAux_zero a 0 n i.val
  · exact ⟨Nat.zero_le i.val, i.isLt, Nat.le_refl n⟩
  · convert h_zero
    simp [Vector.get_eq_getElem]

end DafnySpecs.NpProd