namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]'(by simp [List.mem_range]; exact Nat.lt_of_succ_le (Nat.succ_le_of_lt i.isLt))) 0)

/-- LLM HELPER -/
lemma nat_succ_ne_zero (n : Nat) : n + 1 ≠ 0 := by
  omega

/-- LLM HELPER -/
lemma cumSum_zero_case {n : Nat} (a : Vector Int n) (h : n > 0) :
  (cumSum a)[0]'(Nat.zero_lt_of_ne_zero (Nat.ne_of_gt h)) = a[0]'(Nat.zero_lt_of_ne_zero (Nat.ne_of_gt h)) := by
  simp [cumSum, Vector.get_ofFn]
  simp [List.range_one, List.foldl_cons, List.foldl_nil]

/-- LLM HELPER -/
lemma cumSum_succ_case {n : Nat} (a : Vector Int n) (i : Fin n) (h : i.val > 0) :
  (cumSum a)[i] = (cumSum a)[⟨i.val - 1, Nat.sub_lt i.isLt (Nat.pos_of_ne_zero (Nat.ne_of_gt h))⟩] + a[i] := by
  simp [cumSum, Vector.get_ofFn]
  have h_range : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
    rw [List.range_succ_eq_map]
    simp [List.map_cons, List.map_nil]
  rw [h_range]
  rw [List.foldl_append]
  simp [List.foldl_cons, List.foldl_nil]
  congr 1
  simp [List.range_succ_eq_map]

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumSum a)[0]'(Nat.zero_lt_of_ne_zero (Nat.ne_of_gt (by assumption))) = a[0]'(Nat.zero_lt_of_ne_zero (Nat.ne_of_gt (by assumption)))) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(Nat.sub_lt i.isLt (Nat.pos_of_ne_zero (Nat.ne_of_gt (by assumption)))) + a[i] := by
  constructor
  · intro h_pos
    exact cumSum_zero_case a h_pos
  · intro i hi
    have h_eq : ⟨i.val - 1, Nat.sub_lt i.isLt (Nat.pos_of_ne_zero (Nat.ne_of_gt hi))⟩ = (i.val - 1 : Fin n) := by
      simp [Fin.mk_val]
    rw [← h_eq]
    exact cumSum_succ_case a i hi

end NpCumSum