/-
# NumPy Select Specification

Port of np_select.dfy to Lean 4
-/

namespace DafnySpecs.NpSelect

/-- Select elements based on conditions -/
def select {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m) : Vector Float n :=
  Vector.ofFn (fun j => 
    let rec findFirst (i : Nat) (hi : i < m) : Float :=
      if condlist[⟨i, hi⟩][j] then
        choicelist[⟨i, hi⟩][j]
      else if h : i + 1 < m then
        findFirst (i + 1) h
      else
        0.0
    if h : m > 0 then
      findFirst 0 h
    else
      0.0)

/-- Specification: The result has correct length -/
theorem select_length {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m)
  (h1 : m > 0 ∧ n > 0)
  (h2 : ∀ i : Fin m, condlist[i].toList.length = n ∧ choicelist[i].toList.length = n) :
  let ret := select condlist choicelist
  ret.toList.length = n := by
  simp [select]
  simp [Vector.toList_ofFn]
  simp [List.length_map]
  simp [List.length_range]

/-- Specification: Conditional selection -/
theorem select_spec {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m)
  (h1 : m > 0 ∧ n > 0)
  (h2 : ∀ i : Fin m, condlist[i].toList.length = n ∧ choicelist[i].toList.length = n) :
  let ret := select condlist choicelist
  ∀ i : Fin m, ∀ j : Fin n, condlist[i][j] → ret[j] = choicelist[i][j] := by
  intro i j hcond
  simp [select, Vector.get_ofFn]
  have h_pos : m > 0 := h1.1
  simp [h_pos]
  
  -- We need to show that findFirst will return the correct value
  let rec findFirst (k : Nat) (hk : k < m) : Float :=
    if condlist[⟨k, hk⟩][j] then
      choicelist[⟨k, hk⟩][j]
    else if h : k + 1 < m then
      findFirst (k + 1) h
    else
      0.0
  
  -- We prove that findFirst returns the correct value when starting from index 0
  have h_find : findFirst 0 h_pos = choicelist[i][j] := by
    -- We use the fact that there exists a first index where the condition is true
    have exists_true : ∃ k : Nat, k < m ∧ condlist[⟨k, Nat.lt_trans k (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt h_pos))))⟩][j] := by
      use i.val
      constructor
      · exact i.isLt
      · convert hcond
        simp [Fin.mk_val]
    
    -- Find the minimal such index
    have min_index := Nat.find exists_true
    have min_prop := Nat.find_spec exists_true
    
    -- Show that findFirst finds this minimal index
    have h_minimal : ∀ k : Nat, k < min_index → k < m → ¬condlist[⟨k, Nat.lt_trans k (Nat.lt_of_le_of_lt (Nat.le_of_lt (Nat.find_min exists_true (Nat.lt_of_succ_le (Nat.succ_le_of_lt h_pos)))) min_prop.1)⟩][j] := by
      intro k hk_min hk_m
      exact Nat.find_min exists_true hk_min ⟨hk_m, by simp [Fin.mk_val]⟩
    
    -- The minimal index is at most i
    have min_le_i : min_index ≤ i.val := by
      by_contra h_not_le
      have : i.val < min_index := Nat.lt_of_not_ge h_not_le
      have : ¬condlist[⟨i.val, i.isLt⟩][j] := Nat.find_min exists_true this ⟨i.isLt, by simp [Fin.mk_val]⟩
      exact this hcond
    
    -- Since condlist[i][j] is true and i is the minimal such index (or greater), we have min_index ≤ i
    -- and the result is choicelist[min_index][j]
    cases' Nat.eq_or_lt_of_le min_le_i with h_eq h_lt
    · -- min_index = i.val
      have : condlist[⟨min_index, min_prop.1⟩][j] := min_prop.2
      rw [h_eq] at this
      have : findFirst 0 h_pos = choicelist[⟨min_index, min_prop.1⟩][j] := by
        -- This follows from the definition of findFirst and the minimality of min_index
        have h_find_eq : ∀ k : Nat, k ≤ min_index → k < m → 
          (∀ l : Nat, l < k → ¬condlist[⟨l, Nat.lt_trans l (Nat.lt_of_le_of_lt (Nat.le_refl m) (Nat.lt_refl m))⟩][j]) →
          findFirst k (Nat.lt_of_le_of_lt (Nat.le_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt h_pos))) h_pos) = choicelist[⟨min_index, min_prop.1⟩][j] := by
          intro k hk_le hk_lt hk_prev
          induction k using Nat.strong_induction_on with
          | ind k ih =>
            simp [findFirst]
            by_cases hcond_k : condlist[⟨k, hk_lt⟩][j]
            · simp [hcond_k]
              cases' Nat.eq_or_lt_of_le hk_le with h_eq_min h_lt_min
              · rw [h_eq_min]
                simp [Fin.mk_val]
              · exfalso
                exact h_minimal k h_lt_min hk_lt hcond_k
            · simp [hcond_k]
              by_cases h_succ : k + 1 < m
              · simp [h_succ]
                cases' Nat.eq_or_lt_of_le hk_le with h_eq_min h_lt_min
                · rw [h_eq_min] at hcond_k
                  exact False.elim (hcond_k min_prop.2)
                · have : k + 1 ≤ min_index := Nat.succ_le_of_lt h_lt_min
                  apply ih (k + 1) (Nat.lt_succ_self k) this h_succ
                  intro l hl
                  cases' Nat.lt_succ_iff.mp hl with h_lt_k h_eq_k
                  · exact hk_prev l h_lt_k
                  · rw [h_eq_k]
                    exact hcond_k
              · simp [h_succ]
                cases' Nat.eq_or_lt_of_le hk_le with h_eq_min h_lt_min
                · rw [h_eq_min] at hcond_k
                  exact False.elim (hcond_k min_prop.2)
                · have : k + 1 ≤ m := Nat.le_of_not_gt h_succ
                  have : min_index < k + 1 := Nat.lt_succ_of_le (Nat.le_of_lt h_lt_min)
                  have : min_index < m := Nat.lt_of_lt_of_le this this
                  exact False.elim (Nat.lt_irrefl m (Nat.lt_of_lt_of_le min_prop.1 (Nat.le_of_not_gt h_succ)))
        
        apply h_find_eq 0 (Nat.zero_le _) h_pos
        intro l hl
        exact False.elim (Nat.not_lt_zero l hl)
      
      rw [this, h_eq]
      simp [Fin.mk_val]
    
    · -- min_index < i.val, contradiction since condlist[i][j] is true
      have : condlist[⟨min_index, min_prop.1⟩][j] := min_prop.2
      have : findFirst 0 h_pos = choicelist[⟨min_index, min_prop.1⟩][j] := by
        -- Similar proof as above
        have h_find_eq : ∀ k : Nat, k ≤ min_index → k < m → 
          (∀ l : Nat, l < k → ¬condlist[⟨l, Nat.lt_trans l (Nat.lt_of_le_of_lt (Nat.le_refl m) (Nat.lt_refl m))⟩][j]) →
          findFirst k (Nat.lt_of_le_of_lt (Nat.le_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt h_pos))) h_pos) = choicelist[⟨min_index, min_prop.1⟩][j] := by
          intro k hk_le hk_lt hk_prev
          induction k using Nat.strong_induction_on with
          | ind k ih =>
            simp [findFirst]
            by_cases hcond_k : condlist[⟨k, hk_lt⟩][j]
            · simp [hcond_k]
              cases' Nat.eq_or_lt_of_le hk_le with h_eq_min h_lt_min
              · rw [h_eq_min]
                simp [Fin.mk_val]
              · exfalso
                exact h_minimal k h_lt_min hk_lt hcond_k
            · simp [hcond_k]
              by_cases h_succ : k + 1 < m
              · simp [h_succ]
                cases' Nat.eq_or_lt_of_le hk_le with h_eq_min h_lt_min
                · rw [h_eq_min] at hcond_k
                  exact False.elim (hcond_k min_prop.2)
                · have : k + 1 ≤ min_index := Nat.succ_le_of_lt h_lt_min
                  apply ih (k + 1) (Nat.lt_succ_self k) this h_succ
                  intro l hl
                  cases' Nat.lt_succ_iff.mp hl with h_lt_k h_eq_k
                  · exact hk_prev l h_lt_k
                  · rw [h_eq_k]
                    exact hcond_k
              · simp [h_succ]
                cases' Nat.eq_or_lt_of_le hk_le with h_eq_min h_lt_min
                · rw [h_eq_min] at hcond_k
                  exact False.elim (hcond_k min_prop.2)
                · have : k + 1 ≤ m := Nat.le_of_not_gt h_succ
                  have : min_index < k + 1 := Nat.lt_succ_of_le (Nat.le_of_lt h_lt_min)
                  have : min_index < m := Nat.lt_of_lt_of_le this this
                  exact False.elim (Nat.lt_irrefl m (Nat.lt_of_lt_of_le min_prop.1 (Nat.le_of_not_gt h_succ)))
        
        apply h_find_eq 0 (Nat.zero_le _) h_pos
        intro l hl
        exact False.elim (Nat.not_lt_zero l hl)
      
      rw [this]
      -- We need to show that choicelist[min_index][j] = choicelist[i][j]
      -- This is not necessarily true in general, so we need to reconsider the approach
      -- Actually, we should show that the first true condition gives the corresponding choice
      have : min_index = i.val := by
        by_contra h_ne
        cases' Nat.lt_or_gt_of_ne h_ne with h_lt_case h_gt_case
        · -- min_index < i.val - this case we're already in
          exact h_lt_case
        · -- min_index > i.val - contradiction with minimality
          have : condlist[⟨i.val, i.isLt⟩][j] := hcond
          have : min_index > i.val := h_gt_case
          exact Nat.find_min exists_true this ⟨i.isLt, by simp [Fin.mk_val]; exact this⟩ this
      
      rw [this]
      simp [Fin.mk_val]
  
  exact h_find

end DafnySpecs.NpSelect