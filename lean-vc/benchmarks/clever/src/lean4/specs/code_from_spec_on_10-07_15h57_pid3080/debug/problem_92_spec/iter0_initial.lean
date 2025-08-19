import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Rat → Rat → Rat → Bool)
(a: Rat) (b: Rat) (c: Rat) :=
let spec (result : Bool) :=
  let nums := [a, b, c];
  result = true ↔ ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ (nums[i]! + nums[j]! = nums[k]!) ∧ a.den = 1 ∧ a.den = b.den ∧ a.den = c.den
∃ result,
  implementation a b c = result ∧
  spec result

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool := 
  if a.den = 1 ∧ b.den = 1 ∧ c.den = 1 then
    (a + b = c) ∨ (a + c = b) ∨ (b + c = a)
  else
    false

-- LLM HELPER
lemma list_getElem_eq (a b c : Rat) : 
  ([a, b, c] : List Rat)[0]! = a ∧ 
  ([a, b, c] : List Rat)[1]! = b ∧ 
  ([a, b, c] : List Rat)[2]! = c := by
  simp [List.getElem_cons_succ, List.getElem_cons_zero]

-- LLM HELPER
lemma three_distinct_indices_cases (i j k : ℕ) 
  (h_sub : {i, j, k} ⊆ ({0, 1, 2} : Set ℕ))
  (h_ij : i ≠ j) (h_jk : j ≠ k) (h_ki : k ≠ i) :
  (i = 0 ∧ j = 1 ∧ k = 2) ∨ 
  (i = 0 ∧ j = 2 ∧ k = 1) ∨ 
  (i = 1 ∧ j = 0 ∧ k = 2) ∨ 
  (i = 1 ∧ j = 2 ∧ k = 0) ∨ 
  (i = 2 ∧ j = 0 ∧ k = 1) ∨ 
  (i = 2 ∧ j = 1 ∧ k = 0) := by
  have hi : i ∈ {0, 1, 2} := h_sub (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hj : j ∈ {0, 1, 2} := h_sub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hk : k ∈ {0, 1, 2} := h_sub (Set.mem_singleton _)
  simp at hi hj hk
  interval_cases i <;> interval_cases j <;> interval_cases k <;> 
  simp_all [h_ij, h_jk, h_ki]

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  unfold problem_spec
  let spec := fun result => 
    let nums := [a, b, c]
    result = true ↔ ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ (nums[i]! + nums[j]! = nums[k]!) ∧ a.den = 1 ∧ a.den = b.den ∧ a.den = c.den
  
  use implementation a b c
  constructor
  · rfl
  · unfold implementation
    split_ifs with h
    · simp [spec]
      constructor
      · intro h_true
        cases h with
        | mk h_a h_bc =>
          cases h_bc with
          | mk h_b h_c =>
            cases h_true with
            | inl h_ab_c =>
              use 0, 1, 2
              constructor
              · simp [Set.subset_def]
              constructor
              · norm_num
              constructor
              · norm_num
              constructor
              · norm_num
              constructor
              · simp [list_getElem_eq]
                exact h_ab_c
              constructor
              · exact h_a
              constructor
              · exact h_b
              · exact h_c
            | inr h_rest =>
              cases h_rest with
              | inl h_ac_b =>
                use 0, 2, 1
                constructor
                · simp [Set.subset_def]
                constructor
                · norm_num
                constructor
                · norm_num
                constructor
                · norm_num
                constructor
                · simp [list_getElem_eq]
                  exact h_ac_b
                constructor
                · exact h_a
                constructor
                · exact h_b
                · exact h_c
              | inr h_bc_a =>
                use 1, 2, 0
                constructor
                · simp [Set.subset_def]
                constructor
                · norm_num
                constructor
                · norm_num
                constructor
                · norm_num
                constructor
                · simp [list_getElem_eq]
                  exact h_bc_a
                constructor
                · exact h_a
                constructor
                · exact h_b
                · exact h_c
      · intro ⟨i, j, k, h_sub, h_ij, h_jk, h_ki, h_sum, h_a, h_b, h_c⟩
        have cases := three_distinct_indices_cases i j k h_sub h_ij h_jk h_ki
        cases cases with
        | inl h_012 =>
          cases h_012 with
          | mk h_i h_jk =>
            cases h_jk with
            | mk h_j h_k =>
              subst h_i h_j h_k
              simp [list_getElem_eq] at h_sum
              left
              exact h_sum
        | inr h_rest =>
          cases h_rest with
          | inl h_021 =>
            cases h_021 with
            | mk h_i h_jk =>
              cases h_jk with
              | mk h_j h_k =>
                subst h_i h_j h_k
                simp [list_getElem_eq] at h_sum
                right
                left
                exact h_sum
          | inr h_more =>
            cases h_more with
            | inl h_102 =>
              cases h_102 with
              | mk h_i h_jk =>
                cases h_jk with
                | mk h_j h_k =>
                  subst h_i h_j h_k
                  simp [list_getElem_eq] at h_sum
                  left
                  rw [add_comm]
                  exact h_sum
            | inr h_even_more =>
              cases h_even_more with
              | inl h_120 =>
                cases h_120 with
                | mk h_i h_jk =>
                  cases h_jk with
                  | mk h_j h_k =>
                    subst h_i h_j h_k
                    simp [list_getElem_eq] at h_sum
                    right
                    right
                    exact h_sum
              | inr h_final =>
                cases h_final with
                | inl h_201 =>
                  cases h_201 with
                  | mk h_i h_jk =>
                    cases h_jk with
                    | mk h_j h_k =>
                      subst h_i h_j h_k
                      simp [list_getElem_eq] at h_sum
                      right
                      left
                      rw [add_comm]
                      exact h_sum
                | inr h_210 =>
                  cases h_210 with
                  | mk h_i h_jk =>
                    cases h_jk with
                    | mk h_j h_k =>
                      subst h_i h_j h_k
                      simp [list_getElem_eq] at h_sum
                      right
                      right
                      rw [add_comm]
                      exact h_sum
    · simp [spec]
      intro ⟨i, j, k, h_sub, h_ij, h_jk, h_ki, h_sum, h_a, h_b, h_c⟩
      simp at h
      cases h with
      | inl h_not_a =>
        contradiction
      | inr h_rest =>
        cases h_rest with
        | inl h_not_b =>
          contradiction
        | inr h_not_c =>
          contradiction