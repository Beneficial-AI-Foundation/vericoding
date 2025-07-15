namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]'(Nat.lt_of_lt_of_le (List.mem_range.mp (by assumption : j ∈ List.range (i.val + 1))) (Nat.le_of_lt_succ i.isLt))) 0)

/- LLM HELPER -/
lemma pos_fin_cast {n : Nat} (i : Fin n) (h : i.val > 0) : n > 0 := by
  have : i.val < n := i.isLt
  omega

/- LLM HELPER -/
lemma zero_lt_n {n : Nat} (h : n > 0) : (0 : Fin n).val = 0 := by
  rfl

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by 
    by_cases h : n = 0
    · simp [h] at *
    · omega) = a[0]'(by 
    by_cases h : n = 0
    · simp [h] at *
    · omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by 
    intro i hi
    have : i.val < n := i.isLt
    have : i.val ≥ 1 := hi
    omega) + a[i] := by
  constructor
  · -- First part: (cumSum a)[0] = a[0]
    simp [cumSum]
    rfl
  · -- Second part: recurrence relation
    intro i hi
    simp [cumSum]
    have h_range : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
      rw [List.range_succ]
    rw [h_range]
    rw [List.foldl_append]
    simp [List.foldl_cons, List.foldl_nil]
    have h_eq : i.val - 1 + 1 = i.val := by omega
    rw [h_eq]

end NpCumSum