import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(numbers: List Nat) :=
-- spec
let spec (result: List Nat) :=
(result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1) ∧
(result.length = 2 ↔ ∃ i, i < numbers.length ∧
  numbers[i]! % 2 = 0 ∧
  result[0]! = numbers[i]! ∧
  result[1]! = i ∧
  (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_min_even_aux (numbers: List Nat) (i: Nat) : Option (Nat × Nat) :=
  match i with
  | 0 => none
  | n + 1 => 
    if h : n < numbers.length then
      if numbers[n]! % 2 = 0 then
        match find_min_even_aux numbers n with
        | none => some (numbers[n]!, n)
        | some (val, idx) => 
          if numbers[n]! ≤ val then some (numbers[n]!, n)
          else some (val, idx)
      else find_min_even_aux numbers n
    else find_min_even_aux numbers n

def implementation (numbers: List Nat) : List Nat := 
  match find_min_even_aux numbers numbers.length with
  | none => []
  | some (val, idx) => [val, idx]

-- LLM HELPER
lemma find_min_even_aux_spec (numbers: List Nat) (i: Nat) :
  match find_min_even_aux numbers i with
  | none => ∀ j, j < i → j < numbers.length → numbers[j]! % 2 = 1
  | some (val, idx) => 
    idx < i ∧ idx < numbers.length ∧ numbers[idx]! = val ∧ numbers[idx]! % 2 = 0 ∧
    (∀ j, j < i → j < numbers.length → j < idx → (numbers[j]! % 2 = 1 ∨ val < numbers[j]!)) ∧
    (∀ k, k < i → k < numbers.length → numbers[k]! % 2 = 0 → val ≤ numbers[k]!) := by
  induction i with
  | zero => simp [find_min_even_aux]
  | succ n ih =>
    simp [find_min_even_aux]
    by_cases h : n < numbers.length
    · simp [h]
      by_cases h_even : numbers[n]! % 2 = 0
      · simp [h_even]
        cases h_aux : find_min_even_aux numbers n with
        | none =>
          simp [h_aux]
          constructor
          · exact h
          constructor
          · exact h
          constructor
          · rfl
          constructor
          · exact h_even
          constructor
          · intro j hj_bound hj_len hj_lt
            have hj_n : j < n := hj_lt
            have ih_none := ih
            rw [h_aux] at ih_none
            exact ih_none j hj_n hj_len
          · intro k hk_bound hk_len hk_even
            by_cases hk_n : k < n
            · have ih_none := ih
              rw [h_aux] at ih_none
              exact ih_none k hk_n hk_len hk_even
            · have hk_eq : k = n := by
                omega
              rw [hk_eq]
              le_refl _
        | some val idx =>
          simp
          by_cases h_le : numbers[n]! ≤ val
          · simp [h_le]
            constructor
            · exact h
            constructor
            · exact h
            constructor
            · rfl
            constructor
            · exact h_even
            constructor
            · intro j hj_bound hj_len hj_lt
              by_cases hj_n : j < n
              · have ih_some := ih
                rw [h_aux] at ih_some
                have ⟨_, _, _, _, ih_prop, _⟩ := ih_some
                cases' ih_prop j hj_n hj_len (by omega) with h_odd h_less
                · left; exact h_odd
                · right; exact Nat.lt_of_lt_of_le h_less h_le
              · have hj_eq : j = n := by omega
                right
                rw [hj_eq]
                have ih_some := ih
                rw [h_aux] at ih_some
                have ⟨_, _, ih_val, _, _, _⟩ := ih_some
                rw [← ih_val]
                exact Nat.lt_of_le_of_ne h_le (Ne.symm (Nat.ne_of_lt (Nat.lt_of_le_of_ne h_le (by
                  intro h_eq
                  have ih_some := ih
                  rw [h_aux] at ih_some
                  have ⟨_, _, ih_val, _, _, _⟩ := ih_some
                  rw [ih_val] at h_eq
                  exact absurd h_eq.symm (Nat.ne_of_lt (Nat.lt_of_le_of_ne h_le (by
                    intro; contradiction)))))))
            · intro k hk_bound hk_len hk_even
              by_cases hk_n : k < n
              · have ih_some := ih
                rw [h_aux] at ih_some
                have ⟨_, _, _, _, _, ih_min⟩ := ih_some
                exact Nat.le_trans (ih_min k hk_n hk_len hk_even) h_le
              · have hk_eq : k = n := by omega
                rw [hk_eq]
                le_refl _
          · simp [h_le]
            have ih_some := ih
            rw [h_aux] at ih_some
            have ⟨ih_idx_bound, ih_idx_len, ih_val, ih_even, ih_prop, ih_min⟩ := ih_some
            constructor
            · omega
            constructor
            · exact ih_idx_len
            constructor
            · exact ih_val
            constructor
            · exact ih_even
            constructor
            · intro j hj_bound hj_len hj_lt
              by_cases hj_n : j < n
              · exact ih_prop j hj_n hj_len hj_lt
              · have hj_eq : j = n := by omega
                right
                rw [hj_eq]
                exact Nat.lt_of_not_le h_le
            · intro k hk_bound hk_len hk_even
              by_cases hk_n : k < n
              · exact ih_min k hk_n hk_len hk_even
              · have hk_eq : k = n := by omega
                rw [hk_eq]
                exact Nat.le_of_not_le h_le
      · simp [h_even]
        have ih_result := ih
        cases h_aux : find_min_even_aux numbers n with
        | none =>
          simp [h_aux]
          rw [h_aux] at ih_result
          intro j hj_bound hj_len
          by_cases hj_n : j < n
          · exact ih_result j hj_n hj_len
          · have hj_eq : j = n := by omega
            rw [hj_eq]
            exact h_even
        | some val idx =>
          simp [h_aux]
          rw [h_aux] at ih_result
          have ⟨ih_idx_bound, ih_idx_len, ih_val, ih_even_prop, ih_prop, ih_min⟩ := ih_result
          constructor
          · omega
          constructor
          · exact ih_idx_len
          constructor
          · exact ih_val
          constructor
          · exact ih_even_prop
          constructor
          · intro j hj_bound hj_len hj_lt
            by_cases hj_n : j < n
            · exact ih_prop j hj_n hj_len hj_lt
            · have hj_eq : j = n := by omega
              left
              rw [hj_eq]
              exact h_even
          · intro k hk_bound hk_len hk_even_prop
            by_cases hk_n : k < n
            · exact ih_min k hk_n hk_len hk_even_prop
            · have hk_eq : k = n := by omega
              rw [hk_eq] at hk_even_prop
              exact absurd hk_even_prop h_even
    · simp [h]
      exact ih

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use match find_min_even_aux numbers numbers.length with
      | none => []
      | some (val, idx) => [val, idx]
  constructor
  · rfl
  · simp
    have h_spec := find_min_even_aux_spec numbers numbers.length
    cases h_case : find_min_even_aux numbers numbers.length with
    | none =>
      simp [h_case]
      rw [h_case] at h_spec
      constructor
      · intro h_all_odd
        exact h_all_odd
      · intro h_exists
        obtain ⟨i, hi_bound, hi_even⟩ := h_exists
        exact absurd hi_even (h_spec i hi_bound hi_bound)
    | some val idx =>
      simp [h_case]
      rw [h_case] at h_spec
      have ⟨h_idx_bound, h_idx_len, h_val, h_even, h_prop, h_min⟩ := h_spec
      constructor
      · intro h_all_odd
        exact absurd h_even (h_all_odd idx h_idx_len)
      · use idx
        constructor
        · exact h_idx_len
        constructor
        · exact h_even
        constructor
        · simp [h_val]
        constructor
        · simp
        constructor
        · intro j hj_bound hj_lt
          exact h_prop j hj_bound hj_bound hj_lt
        · intro k hk_bound hk_even_prop
          exact h_min k hk_bound hk_bound hk_even_prop