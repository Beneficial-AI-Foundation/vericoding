namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]!) 0)

/-- LLM HELPER -/
lemma fin_zero_val_zero (n : Nat) (h : n > 0) : (⟨0, h⟩ : Fin n).val = 0 := rfl

/-- LLM HELPER -/
lemma fin_zero_lt (n : Nat) (h : n > 0) : 0 < n := h

/-- LLM HELPER -/
lemma fin_pred_lt (n : Nat) (i : Fin n) (h : i.val > 0) : i.val - 1 < n := by
  omega

/-- LLM HELPER -/
lemma zero_lt_n_of_fin {n : Nat} (i : Fin n) : 0 < n := i.2

/-- LLM HELPER -/
lemma vector_get_ofFn {n : Nat} {α : Type*} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  rw [Vector.get_ofFn]

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumSum a)[0]! = a[0]!) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[⟨i.val - 1, fin_pred_lt n i i.val.gt_zero⟩] + a[i] := by
  constructor
  · -- First part: (cumSum a)[0] = a[0]
    intro h
    simp [cumSum, vector_get_ofFn]
    simp [List.range, List.foldl]
    have h_zero : (⟨0, h⟩ : Fin n).val = 0 := rfl
    simp [h_zero]
    rfl
  · -- Second part: ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1] + a[i]
    intro i hi
    simp [cumSum, vector_get_ofFn]
    have h_range : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
      rw [List.range_succ]
    rw [h_range]
    rw [List.foldl_append]
    simp [List.foldl]
    congr 1
    simp [cumSum, vector_get_ofFn]
    have h_pred : i.val - 1 < n := by omega
    have h_pred_pos : i.val > 0 := hi
    have h_pred_fin : ⟨i.val - 1, h_pred⟩ = ⟨i.val - 1, fin_pred_lt n i h_pred_pos⟩ := by
      simp [Fin.ext_iff]
    rw [h_pred_fin]

end NpCumSum