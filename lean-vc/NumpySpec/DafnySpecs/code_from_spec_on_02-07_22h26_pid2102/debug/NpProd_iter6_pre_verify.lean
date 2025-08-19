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
  omega

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
  prodArrayAux a start finish = List.foldl (fun acc i => acc * a[start + i]'(by omega)) 1 (List.range (finish - start)) := by
  induction' (finish - start) using Nat.strong_induction_on with k ih generalizing start
  by_cases h : start < finish
  · have h_bounds : start < finish ∧ finish ≤ n := ⟨h, h_finish⟩
    simp [prodArrayAux, h_bounds]
    have finish_pos : 0 < finish - start := Nat.sub_pos_of_lt h
    rw [List.range_succ_eq_map (finish - start - 1)]
    simp only [List.foldl_map]
    have : finish - start - 1 + 1 = finish - start := Nat.sub_add_cancel finish_pos
    rw [← this]
    simp [List.range_succ]
    rw [List.foldl_cons]
    simp
    congr 1
    have : start + 1 ≤ finish := Nat.succ_le_of_lt h
    have : finish - (start + 1) = finish - start - 1 := by omega
    rw [← this]
    apply ih (finish - (start + 1))
    omega
    omega
    omega
  · have h_eq : start = finish := Nat.eq_of_le_of_not_lt h_start h
    simp [h_eq, prodArrayAux, List.range_zero, List.foldl_nil]

/-- Specification: prod returns the product of all elements -/
theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n := by
  rfl

/-- Specification: prodArray with valid bounds computes partial product -/
theorem prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h_start : start ≤ finish) (h_finish : finish ≤ n) :
  prodArray a start finish = List.foldl (fun acc i => acc * a[start + i]'(by omega)) 1 (List.range (finish - start)) := by
  unfold prodArray
  rw [if_pos ⟨h_start, h_finish⟩]
  exact prodArrayAux_eq_foldl a start finish h_start h_finish

/-- LLM HELPER -/
lemma prodArrayAux_split {n : Nat} (a : Vector Int n) (start mid finish : Nat)
  (h1 : start ≤ mid) (h2 : mid ≤ finish) (h3 : finish ≤ n) :
  prodArrayAux a start finish = prodArrayAux a start mid * prodArrayAux a mid finish := by
  induction' (finish - start) using Nat.strong_induction_on with k ih generalizing start mid
  by_cases h : start < finish
  · by_cases h_mid : mid < finish
    · have h_bounds : start < finish ∧ finish ≤ n := ⟨h, h3⟩
      simp [prodArrayAux, h_bounds]
      by_cases h_start_mid : start < mid
      · have h_mid_bounds : start < mid ∧ mid ≤ n := ⟨h_start_mid, Nat.le_trans h2 h3⟩
        simp [prodArrayAux, h_mid_bounds]
        rw [mul_assoc]
        congr 1
        apply ih (finish - start - 1)
        omega
        omega
        omega
        omega
      · have h_start_eq_mid : start = mid := Nat.eq_of_le_of_not_lt h1 h_start_mid
        simp [h_start_eq_mid]
        have h_mid_bounds : mid < finish ∧ finish ≤ n := ⟨h_mid, h3⟩
        simp [prodArrayAux, h_mid_bounds]
        simp [one_mul]
    · have h_mid_eq : mid = finish := Nat.eq_of_le_of_not_lt h2 h_mid
      simp [h_mid_eq, prodArrayAux]
      simp [mul_one]
  · have h_start_eq : start = finish := Nat.eq_of_le_of_not_lt (Nat.le_trans h1 h2) h
    simp [h_start_eq, prodArrayAux]
    simp [one_mul]

/-- LLM HELPER -/
theorem prodArray_concat_aux {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prodArray (a ++ b) 0 (m + n) = prodArray (a ++ b) 0 m * prodArray (a ++ b) m (m + n) := by
  unfold prodArray
  rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
  rw [if_pos ⟨Nat.zero_le _, Nat.le_add_right _ _⟩] 
  rw [if_pos ⟨Nat.le_add_right _ _, Nat.le_refl _⟩]
  exact prodArrayAux_split (a ++ b) 0 m (m + n) (Nat.zero_le _) (Nat.le_add_right _ _) (Nat.le_refl _)

/-- LLM HELPER -/
lemma prodArrayAux_append_left {m n : Nat} (a : Vector Int m) (b : Vector Int n) (finish : Nat) (h_finish : finish ≤ m) :
  prodArrayAux (a ++ b) 0 finish = prodArrayAux a 0 finish := by
  induction' finish using Nat.strong_induction_on with finish ih
  by_cases h : 0 < finish
  · have h_bounds : 0 < finish ∧ finish ≤ m + n := ⟨h, Nat.le_trans h_finish (Nat.le_add_right _ _)⟩
    simp [prodArrayAux, h_bounds]
    have h_bounds_a : 0 < finish ∧ finish ≤ m := ⟨h, h_finish⟩
    simp [prodArrayAux, h_bounds_a]
    congr 1
    · simp [Vector.getElem_append_left]
    · apply ih (finish - 1)
      omega
      omega
  · have h_eq : finish = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h)
    simp [h_eq, prodArrayAux]

/-- LLM HELPER -/
lemma prodArrayAux_append_right {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prodArrayAux (a ++ b) m (m + n) = prodArrayAux b 0 n := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h : 0 < n
  · have h_bounds : m < m + n ∧ m + n ≤ m + n := ⟨Nat.lt_add_of_pos_right h, Nat.le_refl _⟩
    simp [prodArrayAux, h_bounds]
    have h_bounds_b : 0 < n ∧ n ≤ n := ⟨h, Nat.le_refl _⟩
    simp [prodArrayAux, h_bounds_b]
    congr 1
    · simp [Vector.getElem_append_right]
    · convert ih (n - 1) (by omega)
      omega
  · have h_eq : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h)
    simp [h_eq, prodArrayAux]

/-- Specification: product is multiplicative with concatenation -/
theorem prod_concat {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  unfold prod
  rw [prodArray_concat_aux]
  congr 1
  · unfold prodArray
    rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
    rw [if_pos ⟨Nat.zero_le _, Nat.le_add_right _ _⟩]
    exact prodArrayAux_append_left a b m (Nat.le_refl _)
  · unfold prodArray
    rw [if_pos ⟨Nat.le_add_right _ _, Nat.le_refl _⟩]
    rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
    exact prodArrayAux_append_right a b

/-- LLM HELPER -/
theorem prodArrayAux_zero {n : Nat} (a : Vector Int n) (start finish : Nat) (i : Nat)
  (h_i_bound : start ≤ i ∧ i < finish ∧ finish ≤ n) (h_zero : a[i]'(by omega) = 0) :
  prodArrayAux a start finish = 0 := by
  induction' (finish - start) using Nat.strong_induction_on with k ih generalizing start
  by_cases h : start < finish
  · have h_bounds : start < finish ∧ finish ≤ n := ⟨h, h_i_bound.2.2⟩
    simp [prodArrayAux, h_bounds]
    cases' Nat.eq_or_lt_of_le h_i_bound.1 with h_eq h_lt
    · simp [← h_eq, h_zero]
    · simp [mul_eq_zero]
      right
      apply ih (finish - start - 1)
      omega
      exact ⟨Nat.le_of_succ_le_succ (Nat.succ_le_of_lt h_lt), Nat.lt_pred_iff.mpr ⟨Nat.ne_of_gt h, h_i_bound.2.1⟩, Nat.pred_le_pred_iff.mpr h_i_bound.2.2⟩
      exact h_zero
  · exfalso
    exact Nat.not_le.mpr h_i_bound.2.1 (Nat.le_of_not_gt h)

/-- Specification: product with a zero element is zero -/
theorem prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h_zero
  unfold prod prodArray
  rw [if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
  apply prodArrayAux_zero a 0 n i.val
  exact ⟨Nat.zero_le i.val, i.isLt, Nat.le_refl n⟩
  exact h_zero

end DafnySpecs.NpProd