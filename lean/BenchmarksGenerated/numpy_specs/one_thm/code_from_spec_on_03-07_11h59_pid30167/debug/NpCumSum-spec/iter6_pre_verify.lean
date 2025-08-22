namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).map (fun j => a[j]'(by
    have h_mem : j ∈ List.range (i.val + 1) := by assumption
    have h_lt : j < i.val + 1 := List.mem_range.mp h_mem
    exact Nat.lt_of_lt_of_le h_lt (Nat.le_of_lt i.isLt)
  )) |>.sum)

/- LLM HELPER -/
lemma fin_zero_val_eq_zero {n : Nat} (h : n > 0) : (0 : Fin n).val = 0 := rfl

/- LLM HELPER -/
lemma range_succ_eq_append (k : Nat) : List.range (k + 1) = List.range k ++ [k] := by
  rw [List.range_succ_eq_map]
  simp [List.range_concat]

/- LLM HELPER -/
lemma fin_sub_one_add_one {n : Nat} (i : Fin n) (hi : i.val > 0) : i.val - 1 + 1 = i.val := 
  Nat.sub_add_cancel (Nat.le_of_lt_succ (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mp hi))))

/- LLM HELPER -/
lemma fin_sub_one_lt {n : Nat} (i : Fin n) (hi : i.val > 0) : i.val - 1 < n := by
  have : i.val < n := i.isLt
  cases' Nat.eq_or_lt_of_le (Nat.le_sub_one_of_lt this) with h h
  · rw [← h]
    exact Nat.sub_lt (Nat.pos_of_ne_zero (ne_of_gt this)) (by norm_num)
  · exact Nat.lt_trans h (Nat.sub_lt (Nat.pos_of_ne_zero (ne_of_gt (Nat.pos_of_ne_zero (ne_of_gt this)))) (by norm_num))

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumSum a)[0] = a[0]) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[⟨i.val - 1, fin_sub_one_lt i ‹i.val > 0›⟩] + a[i] := by
  constructor
  · intro hn
    simp [cumSum, Vector.get_ofFn]
    simp [List.range_one, List.map, List.sum]
  · intro i hi
    simp [cumSum, Vector.get_ofFn]
    have h1 : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
      rw [List.range_succ_eq_map]
      simp [List.range_concat]
    rw [h1]
    simp [List.map_append, List.sum_append]
    congr 1
    simp [fin_sub_one_add_one i hi]

end NpCumSum