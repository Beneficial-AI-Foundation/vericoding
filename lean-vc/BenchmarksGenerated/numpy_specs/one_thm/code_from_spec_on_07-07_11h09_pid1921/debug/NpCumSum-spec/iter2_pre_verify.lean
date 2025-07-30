namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  match n with
  | 0 => Vector.nil
  | m + 1 => 
    let rec cumSumAux (k : Nat) (acc : Int) : Vector Int k :=
      match k with
      | 0 => Vector.nil
      | j + 1 => 
        let newAcc := acc + a[j]'(Nat.lt_succ_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_succ_iff.mpr (Or.inl (Nat.le_refl j))))))
        Vector.cons newAcc (cumSumAux j (acc + a[j]'(Nat.lt_succ_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_succ_iff.mpr (Or.inl (Nat.le_refl j)))))))) 
    cumSumAux (m + 1) 0

-- LLM HELPER
lemma cumSum_length {n : Nat} (a : Vector Int n) : (cumSum a).length = n := by
  induction n with
  | zero => simp [cumSum]
  | succ n ih => 
    simp [cumSum]
    rfl

-- LLM HELPER  
lemma cumSum_get_zero {n : Nat} (a : Vector Int n) (h : n > 0) : 
  (cumSum a)[0]'h = a[0]'h := by
  cases n with
  | zero => omega
  | succ m =>
    simp [cumSum]
    rfl

-- LLM HELPER
lemma cumSum_get_succ {n : Nat} (a : Vector Int n) (i : Fin n) (h : i.val > 0) :
  (cumSum a)[i] = (cumSum a)[i.val - 1]'(Nat.sub_lt h (Nat.zero_lt_one)) + a[i] := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    simp [cumSum]
    sorry

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumSum a)[0]'(Nat.zero_lt_of_ne_zero (Ne.symm (Nat.ne_of_gt ‹n > 0›))) = a[0]'(Nat.zero_lt_of_ne_zero (Ne.symm (Nat.ne_of_gt ‹n > 0›)))) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(Nat.sub_lt ‹i.val > 0› (Nat.zero_lt_one)) + a[i] := by
  constructor
  · intro h
    exact cumSum_get_zero a h
  · intro i h
    exact cumSum_get_succ a i h

end NpCumSum