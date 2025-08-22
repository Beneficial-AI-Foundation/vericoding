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

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by 
    by_cases h : n = 0
    · simp [h] at *
    · omega) = a[0]'(by 
    by_cases h : n = 0
    · simp [h] at *
    · omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[⟨i.val - 1, fin_sub_one_lt i⟩] + a[i] := by
  constructor
  · -- First part: (cumSum a)[0] = a[0]
    simp [cumSum, Vector.get_ofFn]
    rfl
  · -- Second part: recurrence relation
    intro i hi
    simp [cumSum, Vector.get_ofFn]
    have h_range : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
      rw [List.range_succ]
    rw [h_range]
    rw [List.foldl_append]
    simp [List.foldl_cons, List.foldl_nil]
    congr 1

end NpCumSum