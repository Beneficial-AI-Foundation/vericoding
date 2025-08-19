import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.any_aux {n : Nat} (v : Vector Float n) : Nat → Bool
  | 0 => false
  | i + 1 => 
    if h : i < n then
      if v.get ⟨i, h⟩ ≠ 0 then true
      else Vector.any_aux v i
    else false

-- LLM HELPER
instance : DecidableEq Float := by infer_instance

/-- Test whether any element in a vector evaluates to True.
    
    For numeric types, returns true if any element is non-zero.
    Special values like NaN, positive/negative infinity are considered True.
    This follows NumPy's convention where non-zero values are truthy.
    
    This is a reduction operation that performs logical OR across all elements,
    treating non-zero values as True and zero as False. -/
def any {n : Nat} (v : Vector Float n) : Id Bool :=
  return Vector.any_aux v n

-- LLM HELPER
lemma any_aux_spec {n : Nat} (v : Vector Float n) (k : Nat) :
  Vector.any_aux v k = true ↔ ∃ i : Nat, i < k ∧ i < n ∧ v.get ⟨i, by assumption⟩ ≠ 0 := by
  induction k with
  | zero => 
    simp [Vector.any_aux]
  | succ k ih =>
    simp [Vector.any_aux]
    split_ifs with h
    · simp [ih]
      constructor
      · intro h_or
        cases h_or with
        | inl h_ne => exact ⟨k, Nat.lt_succ_self k, h, h_ne⟩
        | inr h_ex => 
          obtain ⟨i, hi_lt_k, hi_lt_n, hi_ne⟩ := h_ex
          exact ⟨i, Nat.lt_succ_of_lt hi_lt_k, hi_lt_n, hi_ne⟩
      · intro ⟨i, hi_lt_succ, hi_lt_n, hi_ne⟩
        cases Nat.lt_succ_iff.mp hi_lt_succ with
        | inl hi_lt_k => exact Or.inr ⟨i, hi_lt_k, hi_lt_n, hi_ne⟩
        | inr hi_eq => 
          rw [hi_eq] at hi_ne
          exact Or.inl hi_ne
    · simp [ih]
      constructor
      · intro ⟨i, hi_lt_k, hi_lt_n, hi_ne⟩
        exact ⟨i, Nat.lt_succ_of_lt hi_lt_k, hi_lt_n, hi_ne⟩
      · intro ⟨i, hi_lt_succ, hi_lt_n, hi_ne⟩
        cases Nat.lt_succ_iff.mp hi_lt_succ with
        | inl hi_lt_k => exact ⟨i, hi_lt_k, hi_lt_n, hi_ne⟩
        | inr hi_eq => 
          rw [hi_eq] at hi_lt_n
          contradiction

-- LLM HELPER
lemma fin_exists_equiv {n : Nat} (P : Fin n → Prop) :
  (∃ i : Fin n, P i) ↔ (∃ i : Nat, i < n ∧ P ⟨i, by assumption⟩) := by
  constructor
  · intro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, hi⟩
  · intro ⟨i, hi_lt, hi_prop⟩
    exact ⟨⟨i, hi_lt⟩, hi_prop⟩

/-- Specification: `any` returns true if and only if at least one element in the vector is non-zero.
    
    The specification captures comprehensive mathematical properties:
    1. Logical equivalence: result is true iff there exists a non-zero element
    2. Completeness: result is false iff all elements are zero
    3. Empty vector behavior: returns false for empty vectors
    4. Monotonicity: adding more elements can only increase the chance of being true
    
    This matches NumPy's behavior where:
    - Non-zero values (including NaN, ±∞) evaluate to True
    - Only zero evaluates to False
    - Empty arrays return False -/
theorem any_spec {n : Nat} (v : Vector Float n) :
    ⦃⌜True⌝⦄
    any v
    ⦃⇓result => ⌜-- Core logical equivalence
                 (result = true ↔ ∃ i : Fin n, v.get i ≠ 0) ∧
                 (result = false ↔ ∀ i : Fin n, v.get i = 0) ∧
                 -- Boundary conditions  
                 (n = 0 → result = false) ∧
                 -- Monotonicity properties
                 (∀ i : Fin n, v.get i = 0 → result = false) ∧
                 (∃ i : Fin n, v.get i ≠ 0 → result = true) ∧
                 -- Logical consistency
                 (result = true ∨ result = false) ∧
                 ¬(result = true ∧ result = false)⌝⦄ := by
  simp [any]
  constructor
  · simp
  · simp
    constructor
    · -- Core logical equivalence part 1
      rw [any_aux_spec, fin_exists_equiv]
      simp
    · constructor
      · -- Core logical equivalence part 2
        rw [any_aux_spec, fin_exists_equiv]
        simp
        constructor
        · intro h i
          by_contra h_ne
          exact h ⟨i.val, i.isLt, h_ne⟩
        · intro h ⟨i, hi_lt, hi_ne⟩
          exact h ⟨i, hi_lt⟩ hi_ne
      · constructor
        · -- Boundary conditions
          intro h_empty
          rw [h_empty, any_aux_spec]
          simp
        · constructor
          · -- Monotonicity part 1
            intro h_all_zero
            rw [any_aux_spec, fin_exists_equiv]
            simp
            intro i hi_lt hi_ne
            exact h_all_zero ⟨i, hi_lt⟩ hi_ne
          · constructor
            · -- Monotonicity part 2
              intro h_exists
              rw [any_aux_spec, fin_exists_equiv]
              simp
              obtain ⟨i, hi_ne⟩ := h_exists
              exact ⟨i.val, i.isLt, hi_ne⟩
            · -- Logical consistency
              simp