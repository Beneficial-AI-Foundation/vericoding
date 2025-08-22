namespace NpSelect

-- LLM HELPER
def select_helper {n : Nat} (condlist : List (Vector Bool n)) (choicelist : List (Vector Float n)) : Vector Float n :=
  match condlist, choicelist with
  | [], [] => Vector.replicate n 0.0
  | cond :: cond_rest, choice :: choice_rest =>
    let partial_result := select_helper cond_rest choice_rest
    Vector.ofFn (fun j => if cond[j] then choice[j] else partial_result[j])
  | _, _ => Vector.replicate n 0.0

def select {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m) : Vector Float n := 
  select_helper condlist.toList choicelist.toList

-- LLM HELPER
lemma select_helper_length {n : Nat} (condlist : List (Vector Bool n)) (choicelist : List (Vector Float n)) :
  (select_helper condlist choicelist).toList.length = n := by
  induction condlist generalizing choicelist with
  | nil => 
    cases choicelist with
    | nil => simp [select_helper, Vector.toList_replicate]
    | cons _ _ => simp [select_helper, Vector.toList_replicate]
  | cons cond cond_rest ih =>
    cases choicelist with
    | nil => simp [select_helper, Vector.toList_replicate]
    | cons choice choice_rest =>
      simp [select_helper]
      rw [Vector.toList_ofFn]
      simp [List.length_ofFn]

-- LLM HELPER
lemma select_helper_spec {n : Nat} (condlist : List (Vector Bool n)) (choicelist : List (Vector Float n))
  (h_len : condlist.length = choicelist.length) :
  let ret := select_helper condlist choicelist
  ∀ (i : Nat) (j : Fin n), i < condlist.length → condlist[i]![j] → ret[j] = choicelist[i]![j] := by
  intro i j hi hcond
  induction condlist generalizing choicelist i with
  | nil => simp at hi
  | cons cond cond_rest ih =>
    cases choicelist with
    | nil => simp at h_len
    | cons choice choice_rest =>
      simp [select_helper]
      cases i with
      | zero => 
        simp at hcond
        simp [Vector.get_ofFn]
        rw [if_pos hcond]
      | succ i' =>
        simp at hi hcond
        rw [Vector.get_ofFn]
        by_cases h : cond[j]
        · simp [h]
        · simp [h]
          apply ih
          · simp at h_len; exact h_len
          · exact Nat.lt_of_succ_lt_succ hi
          · exact hcond

theorem select_spec {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m)
  (h1 : m > 0 ∧ n > 0)
  (h2 : ∀ i : Fin m, condlist[i].toList.length = n ∧ choicelist[i].toList.length = n) :
  let ret := select condlist choicelist
  (ret.toList.length = n) ∧
  (∀ i : Fin m, ∀ j : Fin n, condlist[i][j] → ret[j] = choicelist[i][j]) := by
  constructor
  · simp [select]
    exact select_helper_length condlist.toList choicelist.toList
  · intro i j hcond
    simp [select]
    have h_len : condlist.toList.length = choicelist.toList.length := by
      simp [Vector.length_toList]
    apply select_helper_spec condlist.toList choicelist.toList h_len
    · simp [Vector.length_toList]
      exact i.isLt
    · simp [Vector.get_toList]
      exact hcond

end NpSelect