namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).map (fun j => a[j]!) |>.sum)

/- LLM HELPER -/
lemma fin_zero_val_eq_zero {n : Nat} (h : n > 0) : (0 : Fin n).val = 0 := rfl

/- LLM HELPER -/
lemma range_succ_eq_append (k : Nat) : List.range (k + 1) = List.range k ++ [k] := 
  List.range_succ_eq_map k

/- LLM HELPER -/
lemma fin_sub_one_add_one {n : Nat} (i : Fin n) (hi : i.val > 0) : i.val - 1 + 1 = i.val := 
  Nat.sub_add_cancel (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mp hi)))

/- LLM HELPER -/
lemma fin_sub_one_lt {n : Nat} (i : Fin n) (hi : i.val > 0) : i.val - 1 < n := by
  have : i.val < n := i.isLt
  exact Nat.lt_trans (Nat.sub_lt (Nat.pos_iff_ne_zero.mp hi) (by norm_num)) this

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumSum a)[0]! = a[0]!) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i]! = (cumSum a)[⟨i.val - 1, fin_sub_one_lt i ‹i.val > 0›⟩]! + a[i]! := by
  constructor
  · intro hn
    simp [cumSum, Vector.getElem_ofFn]
    rfl
  · intro i hi
    simp [cumSum, Vector.getElem_ofFn]
    have h1 : List.range (i.val + 1) = List.range i.val ++ [i.val] := List.range_succ i.val
    rw [h1]
    simp [List.map_append, List.sum_append]
    congr 1
    have : i.val - 1 + 1 = i.val := Nat.sub_add_cancel (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mp hi)))
    rw [this]

end NpCumSum