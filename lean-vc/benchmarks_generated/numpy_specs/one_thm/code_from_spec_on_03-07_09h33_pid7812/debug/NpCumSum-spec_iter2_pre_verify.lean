namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]'(by simp [List.mem_range] at *; omega)) 0)

/-- LLM HELPER -/
lemma cumSum_zero_case {n : Nat} (a : Vector Int n) (h : n > 0) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  simp [cumSum, Vector.get_ofFn]
  simp [List.range_one, List.foldl_cons, List.foldl_nil]

/-- LLM HELPER -/
lemma cumSum_succ_case {n : Nat} (a : Vector Int n) (i : Fin n) (h : i.val > 0) :
  (cumSum a)[i] = (cumSum a)[⟨i.val - 1, by omega⟩] + a[i] := by
  simp [cumSum, Vector.get_ofFn]
  have h_range : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
    rw [List.range_succ_eq_map, List.map_range_add]
    simp [List.range_succ]
  rw [h_range]
  rw [List.foldl_append]
  simp [List.foldl_cons, List.foldl_nil]
  congr 1
  simp [List.range_succ_eq_map]

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  constructor
  · -- First part: (cumSum a)[0] = a[0]
    cases' n with n
    · omega
    · exact cumSum_zero_case a (by omega)
  · -- Second part: for i > 0, (cumSum a)[i] = (cumSum a)[i-1] + a[i]
    intro i hi
    have h_eq : ⟨i.val - 1, by omega⟩ = (i.val - 1 : Fin n) := by
      simp [Fin.mk_val]
    rw [← h_eq]
    exact cumSum_succ_case a i hi

end NpCumSum