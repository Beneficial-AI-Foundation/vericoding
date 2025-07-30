namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]!) 0)

/- LLM HELPER -/
lemma pos_fin_cast {n : Nat} (i : Fin n) (h : i.val > 0) : n > 0 := by
  have : i.val < n := i.isLt
  omega

/- LLM HELPER -/
lemma zero_lt_n {n : Nat} (h : n > 0) : (0 : Fin n).val = 0 := by
  rfl

/- LLM HELPER -/
lemma fin_sub_one_lt {n : Nat} (i : Fin n) (hi : i.val > 0) : i.val - 1 < n := by
  have : i.val < n := i.isLt
  omega

/- LLM HELPER -/
lemma fin_sub_one_valid {n : Nat} (i : Fin n) (hi : i.val > 0) : i.val - 1 < n := by
  have : i.val < n := i.isLt
  omega

/- LLM HELPER -/
lemma n_pos_of_fin_exists {n : Nat} (i : Fin n) : n > 0 := by
  exact Nat.pos_of_ne_zero (ne_of_gt i.pos)

/- LLM HELPER -/
lemma n_pos_of_zero_fin {n : Nat} (h : 0 < n) : ∃ (z : Fin n), z.val = 0 := by
  use ⟨0, h⟩
  rfl

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (∀ h : 0 < n, (cumSum a)[⟨0, h⟩] = a[⟨0, h⟩]) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[⟨i.val - 1, fin_sub_one_lt i ‹i.val > 0›⟩] + a[i] := by
  constructor
  · -- First part: (cumSum a)[0] = a[0] when n > 0
    intro h
    simp [cumSum]
    rw [Vector.get_ofFn]
    simp [List.range_one, List.foldl_cons, List.foldl_nil]
    rfl
  · -- Second part: recurrence relation
    intro i hi
    simp [cumSum]
    rw [Vector.get_ofFn, Vector.get_ofFn]
    have h_range : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
      rw [List.range_succ]
    rw [h_range]
    rw [List.foldl_append]
    simp [List.foldl_cons, List.foldl_nil]
    ring

end NpCumSum