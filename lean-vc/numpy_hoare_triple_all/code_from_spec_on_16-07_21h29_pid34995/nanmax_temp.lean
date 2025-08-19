import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Float.nan : Float := 0.0 / 0.0

-- LLM HELPER
lemma Float.nan_isNaN : Float.nan.isNaN = true := by
  simp [Float.nan]
  rfl

-- LLM HELPER
def findNanMax {n : Nat} (a : Vector Float (n + 1)) (idx : Fin (n + 1)) (currentMax : Float) : Float :=
  if idx.val = 0 then
    let elem := a.get idx
    if elem.isNaN then currentMax else
    if currentMax.isNaN then elem else
    max elem currentMax
  else
    let elem := a.get idx
    let newMax := if elem.isNaN then currentMax else
                  if currentMax.isNaN then elem else
                  max elem currentMax
    have h1 : idx.val < n + 1 := idx.isLt
    have h2 : idx.val > 0 := by
      have : idx.val ≠ 0 := by
        intro h
        simp [h]
      exact Nat.pos_of_ne_zero this
    have h : idx.val - 1 < n + 1 := by
      have : idx.val ≥ 1 := h2
      have : idx.val - 1 < idx.val := Nat.sub_lt (Nat.pos_of_ne_zero (ne_of_gt h2)) (by norm_num)
      exact Nat.lt_trans this h1
    findNanMax a ⟨idx.val - 1, h⟩ newMax
termination_by idx.val

def nanmax {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  pure (findNanMax a ⟨n, Nat.lt_succ_self n⟩ Float.nan)

-- LLM HELPER
lemma findNanMax_preserves_non_nan {n : Nat} (a : Vector Float (n + 1)) (idx : Fin (n + 1)) (currentMax : Float) :
  (∃ i : Fin (n + 1), i.val ≤ idx.val ∧ ¬(a.get i).isNaN) ∨ ¬currentMax.isNaN → 
  ¬(findNanMax a idx currentMax).isNaN := by
  intro h
  induction' idx using Fin.induction with
  | h0 => 
    simp [findNanMax]
    cases' h with h1 h2
    · cases' h1 with i hi
      have : i.val = 0 := Nat.eq_zero_of_le_zero hi.1
      simp [this] at hi
      split_ifs
      · exact h2
      · exact hi.2
      · exact h2
    · split_ifs
      · exact h2
      · simp at *
      · exact h2
  | h idx ih =>
    simp [findNanMax]
    split_ifs
    · apply ih
      left
      use idx
      constructor
      · simp
      · assumption
    · apply ih
      right
      simp at *
      assumption
    · apply ih
      right
      simp at *
      have : max (a.get (Nat.succ idx)) currentMax = a.get (Nat.succ idx) ∨ 
             max (a.get (Nat.succ idx)) currentMax = currentMax := by
        exact max_choice (a.get (Nat.succ idx)) currentMax
      cases' this with h1 h2
      · rw [h1]; assumption
      · rw [h2]; assumption

-- LLM HELPER
lemma findNanMax_is_maximum {n : Nat} (a : Vector Float (n + 1)) (idx : Fin (n + 1)) (currentMax : Float) :
  (∀ i : Fin (n + 1), i.val ≤ idx.val ∧ ¬(a.get i).isNaN → a.get i ≤ findNanMax a idx currentMax) := by
  intro i hi
  induction' idx using Fin.induction with
  | h0 =>
    simp [findNanMax]
    have : i.val = 0 := Nat.eq_zero_of_le_zero hi.1
    simp [this] at hi
    split_ifs
    · have : False := hi.2 (by assumption)
      exact False.elim this
    · have : i = ⟨0, Nat.succ_pos n⟩ := by
        ext
        exact this
      simp [this]
      split_ifs
      · simp at *
      · exact le_max_left _ _
  | h idx ih =>
    simp [findNanMax]
    by_cases h : (a.get (Nat.succ idx)).isNaN
    · apply ih
      constructor
      · have : i.val ≤ Nat.succ idx := hi.1
        cases' Nat.le_iff_lt_or_eq.mp this with h1 h2
        · exact Nat.lt_succ_iff.mp h1
        · have : i.val = Nat.succ idx := h2
          have : ¬(a.get i).isNaN := hi.2
          rw [this] at hi
          have : False := hi.2 h
          exact False.elim this
      · exact hi.2
    · by_cases h2 : currentMax.isNaN
      · apply ih
        constructor
        · have : i.val ≤ Nat.succ idx := hi.1
          cases' Nat.le_iff_lt_or_eq.mp this with h1 h2
          · exact Nat.lt_succ_iff.mp h1
          · have : i.val = Nat.succ idx := h2
            have : i = ⟨Nat.succ idx, by simp⟩ := by
              ext
              exact this
            simp [this]
            exact le_refl _
        · exact hi.2
      · apply ih
        constructor
        · have : i.val ≤ Nat.succ idx := hi.1
          cases' Nat.le_iff_lt_or_eq.mp this with h1 h2
          · exact Nat.lt_succ_iff.mp h1
          · have : i.val = Nat.succ idx := h2
            have : i = ⟨Nat.succ idx, by simp⟩ := by
              ext
              exact this
            simp [this]
            exact le_max_left _ _
        · exact hi.2

-- LLM HELPER
lemma findNanMax_exists_witness {n : Nat} (a : Vector Float (n + 1)) (idx : Fin (n + 1)) (currentMax : Float) :
  ¬(findNanMax a idx currentMax).isNaN → 
  (∃ witness : Fin (n + 1), witness.val ≤ idx.val ∧ findNanMax a idx currentMax = a.get witness) ∨ 
  findNanMax a idx currentMax = currentMax := by
  intro h
  induction' idx using Fin.induction with
  | h0 =>
    simp [findNanMax] at h ⊢
    split_ifs with h1 h2
    · right; rfl
    · left
      use ⟨0, Nat.succ_pos n⟩
      constructor
      · simp
      · rfl
    · right; rfl
  | h idx ih =>
    simp [findNanMax] at h ⊢
    by_cases h1 : (a.get (Nat.succ idx)).isNaN
    · simp [h1] at h ⊢
      have := ih h
      cases' this with h2 h3
      · left
        cases' h2 with witness hw
        use witness
        constructor
        · exact Nat.le_succ_of_le hw.1
        · exact hw.2
      · right
        exact h3
    · by_cases h2 : currentMax.isNaN
      · simp [h1, h2] at h ⊢
        left
        use ⟨Nat.succ idx, by simp⟩
        constructor
        · simp
        · rfl
      · simp [h1, h2] at h ⊢
        have := ih (by simp at h; exact h)
        cases' this with h3 h4
        · left
          cases' h3 with witness hw
          use witness
          constructor
          · exact Nat.le_succ_of_le hw.1
          · exact hw.2
        · right
          exact h4

-- LLM HELPER
lemma all_nan_implies_result_nan {n : Nat} (a : Vector Float (n + 1)) :
  (∀ i : Fin (n + 1), (a.get i).isNaN) → (findNanMax a ⟨n, Nat.lt_succ_self n⟩ Float.nan).isNaN := by
  intro h
  induction' n with n ih
  | zero =>
    simp [findNanMax]
    exact h ⟨0, Nat.succ_pos 0⟩
  | succ =>
    simp [findNanMax]
    have : (a.get ⟨Nat.succ n, Nat.lt_succ_self (Nat.succ n)⟩).isNaN := 
      h ⟨Nat.succ n, Nat.lt_succ_self (Nat.succ n)⟩
    simp [this]
    apply ih
    intro i
    exact h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

theorem nanmax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    nanmax a
    ⦃⇓result => ⌜-- Case 1: If there exists at least one non-NaN element
                 ((∃ i : Fin (n + 1), ¬result.isNaN ∧ ¬(a.get i).isNaN) →
                   (∃ max_idx : Fin (n + 1), 
                     result = a.get max_idx ∧ 
                     ¬(a.get max_idx).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ result))) ∧
                 -- Case 2: If all elements are NaN, result is NaN
                 ((∀ i : Fin (n + 1), (a.get i).isNaN) → result.isNaN) ∧
                 -- Case 3: NaN values are ignored (result is max of non-NaN elements)
                 (¬result.isNaN → 
                   (∃ witness : Fin (n + 1), 
                     result = a.get witness ∧ 
                     ¬(a.get witness).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ result))) ∧
                 -- Case 4: For vectors without NaN, behaves like regular max
                 ((∀ i : Fin (n + 1), ¬(a.get i).isNaN) → 
                   (∃ max_idx : Fin (n + 1),
                     result = a.get max_idx ∧
                     (∀ j : Fin (n + 1), a.get j ≤ result))) ∧
                 -- Sanity check: result is either NaN or exists in the vector
                 (result.isNaN ∨ (∃ witness : Fin (n + 1), result = a.get witness))⌝⦄ := by
  simp [nanmax]
  apply wp_pure
  constructor
  · -- Case 1
    intro h
    cases' h with i hi
    have h_not_nan : ¬(findNanMax a ⟨n, Nat.lt_succ_self n⟩ Float.nan).isNaN := hi.1
    have h_witness := findNanMax_exists_witness a ⟨n, Nat.lt_succ_self n⟩ Float.nan h_not_nan
    cases' h_witness with h1 h2
    · cases' h1 with witness hw
      use witness
      constructor
      · exact hw.2
      constructor
      · rw [← hw.2]
        exact h_not_nan
      · intro j hj
        have : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
        apply findNanMax_is_maximum
        exact ⟨this, hj⟩
    · have : Float.nan.isNaN = true := Float.nan_isNaN
      rw [h2] at h_not_nan
      simp [this] at h_not_nan
  constructor
  · -- Case 2
    intro h
    exact all_nan_implies_result_nan a h
  constructor
  · -- Case 3
    intro h
    have h_witness := findNanMax_exists_witness a ⟨n, Nat.lt_succ_self n⟩ Float.nan h
    cases' h_witness with h1 h2
    · cases' h1 with witness hw
      use witness
      constructor
      · exact hw.2
      constructor
      · rw [← hw.2]
        exact h
      · intro j hj
        have : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
        apply findNanMax_is_maximum
        exact ⟨this, hj⟩
    · have : Float.nan.isNaN = true := Float.nan_isNaN
      rw [h2] at h
      simp [this] at h
  constructor
  · -- Case 4
    intro h
    have h_not_nan : ¬(findNanMax a ⟨n, Nat.lt_succ_self n⟩ Float.nan).isNaN := by
      apply findNanMax_preserves_non_nan
      left
      use ⟨0, Nat.succ_pos n⟩
      constructor
      · simp
      · exact h ⟨0, Nat.succ_pos n⟩
    have h_witness := findNanMax_exists_witness a ⟨n, Nat.lt_succ_self n⟩ Float.nan h_not_nan
    cases' h_witness with h1 h2
    · cases' h1 with witness hw
      use witness
      constructor
      · exact hw.2
      · intro j
        have : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
        apply findNanMax_is_maximum
        exact ⟨this, h j⟩
    · have : Float.nan.isNaN = true := Float.nan_isNaN
      rw [h2] at h_not_nan
      simp [this] at h_not_nan
  · -- Sanity check
    by_cases h : (findNanMax a ⟨n, Nat.lt_succ_self n⟩ Float.nan).isNaN
    · left
      exact h
    · right
      have h_witness := findNanMax_exists_witness a ⟨n, Nat.lt_succ_self n⟩ Float.nan h
      cases' h_witness with h1 h2
      · cases' h1 with witness hw
        use witness
        exact hw.2
      · have : Float.nan.isNaN = true := Float.nan_isNaN
        rw [h2] at h
        simp [this] at h