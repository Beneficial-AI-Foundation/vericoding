namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]'(by omega)) 0)

/- LLM HELPER -/
theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  constructor
  · -- First part: (cumSum a)[0] = a[0]
    simp [cumSum]
    simp [Vector.get_ofFn]
    simp [List.range]
    simp [List.foldl]
  · -- Second part: for i > 0, (cumSum a)[i] = (cumSum a)[i-1] + a[i]
    intro i hi
    simp [cumSum]
    simp [Vector.get_ofFn]
    have h_pos : i.val > 0 := hi
    have h_sub : i.val - 1 < n := by omega
    simp [List.range_succ_eq_map]
    rw [List.foldl_append]
    simp [List.foldl]
    congr 1
    simp [List.range_succ_eq_map]
    rw [List.foldl_append]
    simp [List.foldl]

end NpCumSum