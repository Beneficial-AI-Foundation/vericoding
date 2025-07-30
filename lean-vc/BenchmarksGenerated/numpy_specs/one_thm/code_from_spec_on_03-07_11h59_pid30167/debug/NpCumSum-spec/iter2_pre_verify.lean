namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).map (fun j => a[j]'(Nat.lt_of_lt_of_le (List.mem_range.mp (List.mem_of_mem_map_of_inj Nat.cast_injective (by sorry))) i.isLt)) |>.sum)

/- LLM HELPER -/
lemma fin_zero_val_eq_zero {n : Nat} (h : n > 0) : (0 : Fin n).val = 0 := rfl

/- LLM HELPER -/
lemma range_succ_eq_append (k : Nat) : List.range (k + 1) = List.range k ++ [k] := by
  rw [List.range_succ_eq_map]
  simp [List.range_concat]

/- LLM HELPER -/
lemma fin_sub_one_add_one {n : Nat} (i : Fin n) (hi : i.val > 0) : i.val - 1 + 1 = i.val := 
  Nat.sub_add_cancel (Nat.le_of_lt_succ (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mp hi))))

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by cases n with | zero => simp [Vector.get] | succ n => simp) = a[0]'(by cases n with | zero => simp [Vector.get] | succ n => simp) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by 
    intro i hi
    cases n with 
    | zero => simp at i
    | succ n => 
      have : i.val - 1 < n + 1 := by
        have : i.val ≤ n := Nat.le_of_lt_succ i.isLt
        cases' Nat.eq_or_lt_of_le this with h h
        · rw [← h]; simp [Nat.sub_self]
        · exact Nat.sub_lt_self (Nat.pos_of_ne_zero (ne_of_gt hi)) 1
      exact this) + a[i] := by
  constructor
  · cases n with
    | zero => simp [cumSum, Vector.get]
    | succ n => 
      simp [cumSum, Vector.ofFn_get]
      simp [List.range_one, List.map, List.sum]
  · intro i hi
    simp [cumSum, Vector.ofFn_get]
    have h1 : List.range (i.val + 1) = List.range i.val ++ [i.val] := range_succ_eq_append i.val
    rw [h1]
    simp [List.map_append, List.sum_append]
    congr 1
    simp [fin_sub_one_add_one i hi]

end NpCumSum