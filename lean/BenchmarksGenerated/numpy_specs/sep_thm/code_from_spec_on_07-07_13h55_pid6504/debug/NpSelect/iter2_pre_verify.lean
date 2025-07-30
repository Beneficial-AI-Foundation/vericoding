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
      else if i + 1 < m then
        findFirst (i + 1) (Nat.lt_of_succ_lt hi)
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
    else if k + 1 < m then
      findFirst (k + 1) (Nat.lt_of_succ_lt hk)
    else
      0.0
  
  -- We prove by strong induction that findFirst returns the correct value
  have h_find : ∀ k : Nat, ∀ hk : k < m, k ≤ i.val → 
    (∀ l : Nat, l < k → ¬condlist[⟨l, Nat.lt_trans l hk⟩][j]) →
    findFirst k hk = choicelist[i][j] := by
    intro k hk hki hprev
    simp [findFirst]
    by_cases hcond_k : condlist[⟨k, hk⟩][j]
    · simp [hcond_k]
      cases' Nat.eq_or_lt_of_le hki with heq hlt
      · rw [heq]
        exact hcond
      · exfalso
        have : k < i.val := hlt
        have : k < m := hk
        have : condlist[⟨k, hk⟩][j] = condlist[⟨i.val, i.isLt⟩][j] := by
          rw [Fin.mk_val]
        rw [this] at hcond_k
        exact hcond_k
    · simp [hcond_k]
      by_cases hk_succ : k + 1 < m
      · simp [hk_succ]
        cases' Nat.eq_or_lt_of_le hki with heq hlt
        · rw [heq] at hcond_k
          rw [Fin.mk_val] at hcond_k
          exact False.elim (hcond_k hcond)
        · have : k + 1 ≤ i.val := Nat.succ_le_of_lt hlt
          have : ∀ l : Nat, l < k + 1 → ¬condlist[⟨l, Nat.lt_trans l hk_succ⟩][j] := by
            intro l hl
            cases' Nat.lt_succ_iff.mp hl with h h
            · exact hprev l h
            · rw [h]
              exact hcond_k
          exact this
      · simp [hk_succ]
        cases' Nat.eq_or_lt_of_le hki with heq hlt
        · rw [heq] at hcond_k
          rw [Fin.mk_val] at hcond_k
          exact False.elim (hcond_k hcond)
        · have : k + 1 ≤ m := Nat.le_of_not_gt hk_succ
          have : i.val < k + 1 := Nat.lt_succ_of_le (Nat.le_of_lt hlt)
          have : i.val < m := i.isLt
          have : k + 1 = m := Nat.eq_of_le_of_lt_succ this (Nat.lt_succ_of_le this)
          have : i.val < m := this.trans_eq this.symm
          exact False.elim (Nat.lt_irrefl m (this.trans_le this))

  apply h_find 0 h_pos (Nat.zero_le _)
  intro l hl
  exfalso
  exact Nat.not_lt_zero l hl

end DafnySpecs.NpSelect