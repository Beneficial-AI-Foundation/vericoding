import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermite_product_coeff (m n : Nat) (c1 : Vector Float m) (c2 : Vector Float n) (k : Nat) : Float :=
  if m = 0 ∨ n = 0 then 0
  else
    let rec sum_helper (i : Nat) (acc : Float) : Float :=
      if i >= min (k + 1) m then acc
      else if k ≥ i ∧ k - i < n then
        sum_helper (i + 1) (acc + c1.get ⟨i, Nat.mod_two_eq_zero_or_one i ▸ Nat.zero_lt_succ _⟩ * c2.get ⟨k - i, Nat.mod_two_eq_zero_or_one (k - i) ▸ Nat.zero_lt_succ _⟩)
      else
        sum_helper (i + 1) acc
    sum_helper 0 0.0

-- LLM HELPER
def vector_from_fn {α : Type} (n : Nat) (f : Fin n → α) : Vector α n :=
  ⟨Array.ofFn f, Array.size_ofFn⟩

def hermmul (m n : Nat) (c1 : Vector Float m) (c2 : Vector Float n) : 
    Id (Vector Float (if m = 0 ∨ n = 0 then 1 else m + n - 1)) :=
  if h : m = 0 ∨ n = 0 then
    have h_size : (if m = 0 ∨ n = 0 then 1 else m + n - 1) = 1 := by simp [h]
    h_size ▸ pure (vector_from_fn 1 (fun _ => (0 : Float)))
  else
    let result_size := m + n - 1
    have h_size : (if m = 0 ∨ n = 0 then 1 else m + n - 1) = result_size := by simp [h]
    h_size ▸ pure (vector_from_fn result_size (fun k => hermite_product_coeff m n c1 c2 k.val))

-- LLM HELPER
lemma vector_get_zero_lt_one : 0 < 1 := Nat.one_pos

-- LLM HELPER
lemma not_empty_implies_pos (m n : Nat) (h : ¬(m = 0 ∨ n = 0)) : m > 0 ∧ n > 0 := by
  simp at h
  exact h

-- LLM HELPER
lemma empty_case_size (m n : Nat) (h : m = 0 ∨ n = 0) : 
  (if m = 0 ∨ n = 0 then 1 else m + n - 1) = 1 := by
  simp [h]

-- LLM HELPER
lemma non_empty_case_size (m n : Nat) (h : ¬(m = 0 ∨ n = 0)) : 
  (if m = 0 ∨ n = 0 then 1 else m + n - 1) = m + n - 1 := by
  simp [h]

-- LLM HELPER
lemma fin_cast_lt (i : Fin m) (h : ¬(m = 0 ∨ n = 0)) : 
  i.val < (if m = 0 ∨ n = 0 then 1 else m + n - 1) := by
  rw [non_empty_case_size m n h]
  have hm : m > 0 := by simp at h; exact h.1
  have hn : n > 0 := by simp at h; exact h.2
  have : m + n - 1 ≥ m := by
    have : n ≥ 1 := hn
    omega
  exact Nat.lt_of_lt_of_le i.property this

-- LLM HELPER
lemma fin_cast_lt_2 (i : Fin n) (h : ¬(m = 0 ∨ n = 0)) : 
  i.val < (if m = 0 ∨ n = 0 then 1 else m + n - 1) := by
  rw [non_empty_case_size m n h]
  have hm : m > 0 := by simp at h; exact h.1
  have hn : n > 0 := by simp at h; exact h.2
  have : m + n - 1 ≥ n := by
    have : m ≥ 1 := hm
    omega
  exact Nat.lt_of_lt_of_le i.property this

-- LLM HELPER
lemma pos_fin_exists (n : Nat) (h : n > 0) : ∃ (p : 0 < n), True := by
  use h
  trivial

-- LLM HELPER
lemma zero_lt_m_from_not_empty (m n : Nat) (h : ¬(m = 0 ∨ n = 0)) : 0 < m := by
  simp at h
  exact h.1

-- LLM HELPER
lemma zero_lt_n_from_not_empty (m n : Nat) (h : ¬(m = 0 ∨ n = 0)) : 0 < n := by
  simp at h
  exact h.2

theorem hermmul_spec (m n : Nat) (c1 : Vector Float m) (c2 : Vector Float n) :
    ⦃⌜True⌝⦄
    hermmul m n c1 c2
    ⦃⇓result => ⌜
      -- Empty input handling
      ((m = 0 ∨ n = 0) → result.size = 1 ∧ result.get ⟨0, vector_get_zero_lt_one⟩ = 0) ∧
      -- Non-empty inputs have correct output size
      (m > 0 ∧ n > 0 → result.size = m + n - 1) ∧
      -- Multiplication by constant polynomial (degree 0)
      (n = 1 ∧ m > 0 → ∀ i : Fin m, 
        result.get ⟨i.val, fin_cast_lt i (by simp [Nat.pos_iff_ne_zero.mp ‹m > 0›, ‹n = 1›])⟩ = c1.get i * c2.get ⟨0, zero_lt_n_from_not_empty m n (by simp [Nat.pos_iff_ne_zero.mp ‹m > 0›, ‹n = 1›])⟩) ∧
      (m = 1 ∧ n > 0 → ∀ i : Fin n, 
        result.get ⟨i.val, fin_cast_lt_2 i (by simp [‹m = 1›, Nat.pos_iff_ne_zero.mp ‹n > 0›])⟩ = c2.get i * c1.get ⟨0, zero_lt_m_from_not_empty m n (by simp [‹m = 1›, Nat.pos_iff_ne_zero.mp ‹n > 0›])⟩) ∧
      -- Zero polynomial property
      ((∀ i : Fin m, c1.get i = 0) ∨ (∀ j : Fin n, c2.get j = 0) → 
        ∀ k : Fin result.size, result.get k = 0)
    ⌝⦄ := by
  simp [hermmul]
  intro
  constructor
  · intro h_empty
    simp [vector_from_fn]
    have h_size : (if m = 0 ∨ n = 0 then 1 else m + n - 1) = 1 := by simp [h_empty]
    constructor
    · simp [h_size]
    · simp [Array.get_ofFn]
  · constructor
    · intro h_pos
      by_cases h : m = 0 ∨ n = 0
      · cases h with
        | inl hm => simp [hm] at h_pos
        | inr hn => simp [hn] at h_pos
      · simp [h, vector_from_fn]
        simp [non_empty_case_size m n h]
    · constructor
      · intro ⟨hn_eq, hm_pos⟩
        intro i
        have h : ¬(m = 0 ∨ n = 0) := by simp [Nat.pos_iff_ne_zero.mp hm_pos, hn_eq]
        simp [h, vector_from_fn]
        simp [Array.get_ofFn, hermite_product_coeff, h]
        rw [hn_eq]
        simp [hermite_product_coeff]
        simp [h]
        rfl
      · constructor
        · intro ⟨hm_eq, hn_pos⟩
          intro i
          have h : ¬(m = 0 ∨ n = 0) := by simp [hm_eq, Nat.pos_iff_ne_zero.mp hn_pos]
          simp [h, vector_from_fn]
          simp [Array.get_ofFn, hermite_product_coeff, h]
          rw [hm_eq]
          simp [hermite_product_coeff]
          simp [h]
          rfl
        · intro h_zero
          intro k
          by_cases h : m = 0 ∨ n = 0
          · simp [h, vector_from_fn]
            simp [Array.get_ofFn]
          · simp [h, vector_from_fn]
            simp [Array.get_ofFn, hermite_product_coeff]
            simp [h]
            rfl