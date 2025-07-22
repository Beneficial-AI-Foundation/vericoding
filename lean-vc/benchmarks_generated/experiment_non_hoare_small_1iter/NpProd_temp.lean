/-
# NumPy Product Specification

Port of np_prod.dfy to Lean 4
-/

namespace DafnySpecs.NpProd

-- LLM HELPER
def prodRange (l : List Int) : Int := l.foldl (· * ·) 1

/-- Product of all elements in a vector -/
def prod {n : Nat} (a : Vector Int n) : Int := prodRange a.toList

/-- Helper function: product of elements from start to end (exclusive) -/
def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≥ finish then 1 
  else prodRange (a.toList.drop start |>.take (finish - start))

-- LLM HELPER
lemma list_range_foldl_eq_drop_take {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(by
    have h1 : start + i < start + (finish - start) := by
      simp only [Nat.add_sub_cancel']
      exact Nat.add_lt_add_left (List.mem_range.mp (by assumption)) start
    have h2 : start + (finish - start) = finish := Nat.add_sub_cancel' h_start
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 h_finish
  )) 1 = prodRange (a.toList.drop start |>.take (finish - start)) := by
  induction' finish - start with k ih generalizing start
  · simp [prodRange, List.foldl]
  · simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h_eq : a.toList.drop start |>.take (k + 1) = 
      a[start]'(by exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ k)) 
        (by rw [Nat.add_sub_cancel' h_start]; exact h_finish)) :: 
      (a.toList.drop (start + 1) |>.take k) := by
      rw [List.take_succ_drop_eq_cons]
      simp only [Vector.get_toList]
    rw [h_eq, prodRange, List.foldl_cons]
    congr 1
    have h_shift : finish - start = k + 1 := rfl
    have h_start' : start + 1 ≤ finish := by
      rw [← h_shift]
      exact Nat.add_le_add_right h_start 1
    have h_finish' : finish ≤ n := h_finish
    sorry -- Complex induction step

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  simp only [prod, prodArray]
  simp only [Nat.zero_le, not_le, Nat.lt_irrefl, if_false]
  simp only [List.drop_zero, Nat.sub_zero]
  rw [List.take_length_le]
  simp only [Vector.length_toList]

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'sorry) 1 := by
  simp only [prodArray]
  rw [if_neg (not_le.mpr (Nat.lt_of_le_of_ne h_start (fun h => by
    rw [h] at h_start
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_ne h_start (Ne.symm (ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne h_start (Ne.symm (ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne h_start (fun h => by simp [h] at h_start; exact Nat.lt_irrefl _ h_start))))))))
  )))]
  sorry -- Use list_range_foldl_eq_drop_take helper

-- LLM HELPER
lemma prod_append_eq_prod_mul {l1 l2 : List Int} : 
  prodRange (l1 ++ l2) = prodRange l1 * prodRange l2 := by
  simp only [prodRange]
  rw [List.foldl_append]
  induction' l2 with h t ih generalizing l1
  · simp
  · simp only [List.foldl_cons]
    rw [← ih]
    simp only [List.foldl_cons, mul_assoc]

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  simp only [prod]
  rw [Vector.toList_append]
  exact prod_append_eq_prod_mul

-- LLM HELPER
lemma prod_zero_mem {l : List Int} (h : 0 ∈ l) : prodRange l = 0 := by
  simp only [prodRange]
  induction' l with h t ih
  · exact False.elim (List.not_mem_nil 0 h)
  · simp only [List.foldl_cons, List.mem_cons] at h ⊢
    cases' h with h1 h2
    · rw [h1, zero_mul]
    · rw [ih h2, mul_zero]

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h
  simp only [prod]
  apply prod_zero_mem
  rw [← h]
  exact Vector.mem_toList_of_getElem a i

end DafnySpecs.NpProd