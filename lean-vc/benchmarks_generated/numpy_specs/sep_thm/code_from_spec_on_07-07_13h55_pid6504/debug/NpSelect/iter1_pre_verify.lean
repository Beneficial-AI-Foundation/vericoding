/-
# NumPy Select Specification

Port of np_select.dfy to Lean 4
-/

namespace DafnySpecs.NpSelect

-- LLM HELPER
def selectAux {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m) (j : Fin n) : Float :=
  let rec findFirst (i : Fin m) : Float :=
    if condlist[i][j] then
      choicelist[i][j]
    else if i.val + 1 < m then
      findFirst ⟨i.val + 1, Nat.lt_trans (Nat.lt_succ_self i.val) i.isLt⟩
    else
      0.0
  if m > 0 then
    findFirst ⟨0, Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_ne_zero (ne_of_gt (Nat.zero_lt_of_ne_zero (ne_of_gt h))))⟩
  else
    0.0
  where h : m > 0 := by
    cases' Nat.eq_zero_or_pos m with h h
    · simp [h] at *
      sorry
    · exact h

/-- Select elements based on conditions -/
def select {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m) : Vector Float n :=
  Vector.ofFn (fun j => 
    let rec findFirst (i : Nat) (hi : i < m) : Float :=
      if condlist[⟨i, hi⟩][j] then
        choicelist[⟨i, hi⟩][j]
      else if i + 1 < m then
        findFirst (i + 1) (Nat.lt_of_succ_lt_succ (Nat.succ_lt_of_lt_succ hi))
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
      findFirst (k + 1) (Nat.lt_of_succ_lt_succ (Nat.succ_lt_of_lt_succ hk))
    else
      0.0
  
  -- If condition at position i is true, we need to show findFirst returns the right value
  suffices h : ∀ k : Nat, ∀ hk : k < m, k ≤ i.val → 
    (∀ l : Nat, ∀ hl : l < m, k ≤ l → l < i.val → ¬condlist[⟨l, hl⟩][j]) →
    findFirst k hk = choicelist[i][j] by
    apply h 0 h_pos (Nat.zero_le _)
    intro l hl hkl hli
    exfalso
    simp at hkl hli
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hli (Nat.zero_le _))
  
  intro k hk hki hprev
  simp [findFirst]
  by_cases hcond_k : condlist[⟨k, hk⟩][j]
  · simp [hcond_k]
    cases' Nat.eq_or_lt_of_le hki with heq hlt
    · simp [heq.symm]
      exact hcond
    · exfalso
      have := hprev k hk (le_refl _) hlt
      exact this hcond_k
  · simp [hcond_k]
    by_cases hk_succ : k + 1 < m
    · simp [hk_succ]
      cases' Nat.eq_or_lt_of_le hki with heq hlt
      · simp [heq.symm] at hcond_k
        exact False.elim (hcond_k hcond)
      · sorry -- Need to continue the induction
    · simp [hk_succ]
      cases' Nat.eq_or_lt_of_le hki with heq hlt
      · simp [heq.symm] at hcond_k
        exact False.elim (hcond_k hcond)
      · have : k + 1 ≤ i.val := Nat.succ_le_of_lt hlt
        have : k + 1 ≤ m := Nat.le_of_not_gt hk_succ
        have : i.val < m := i.isLt
        have : k + 1 = m := Nat.eq_of_le_of_lt_succ this (Nat.lt_succ_of_le this)
        have : i.val < k + 1 := Nat.lt_of_le_of_ne this (Ne.symm (Nat.ne_of_lt hlt))
        have : i.val < m := this.trans_eq this.symm
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le this (Nat.le_of_not_gt hk_succ)))

end DafnySpecs.NpSelect