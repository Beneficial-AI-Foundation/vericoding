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

-- LLM HELPER
def is_integer (r : Rat) : Bool := r.den = 1

-- LLM HELPER
def check_sum_condition (a b c : Rat) : Bool :=
  (a + b = c) ∨ (a + c = b) ∨ (b + c = a)

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool := 
  is_integer a ∧ is_integer b ∧ is_integer c ∧ check_sum_condition a b c

-- LLM HELPER
lemma exists_indices_iff (a b c : Rat) :
  (∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ ([a, b, c][i]! + [a, b, c][j]! = [a, b, c][k]!)) ↔ 
  ((a + b = c) ∨ (a + c = b) ∨ (b + c = a)) := by
  constructor
  · intro ⟨i, j, k, h_sub, h_ij, h_jk, h_ki, h_sum⟩
    have h_i : i ∈ {0, 1, 2} := h_sub (Set.mem_insert _ _)
    have h_j : j ∈ {0, 1, 2} := h_sub (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have h_k : k ∈ {0, 1, 2} := h_sub (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have i_cases : i = 0 ∨ i = 1 ∨ i = 2 := by
      cases' h_i with h h
      · left; exact h
      · cases' h with h h
        · right; left; exact h
        · right; right; exact h
    have j_cases : j = 0 ∨ j = 1 ∨ j = 2 := by
      cases' h_j with h h
      · left; exact h
      · cases' h with h h
        · right; left; exact h
        · right; right; exact h
    have k_cases : k = 0 ∨ k = 1 ∨ k = 2 := by
      cases' h_k with h h
      · left; exact h
      · cases' h with h h
        · right; left; exact h
        · right; right; exact h
    cases' i_cases with hi hi
    · cases' j_cases with hj hj
      · subst hi hj; contradiction
      · cases' hj with hj hj
        · cases' k_cases with hk hk
          · subst hi hj hk; contradiction
          · subst hi hj hk; contradiction
          · subst hi hj hk
            simp [List.get!] at h_sum
            left; exact h_sum
        · cases' k_cases with hk hk
          · subst hi hj hk; contradiction
          · subst hi hj hk
            simp [List.get!] at h_sum
            right; left; exact h_sum
          · subst hi hj hk; contradiction
    · cases' hi with hi hi
      · cases' j_cases with hj hj
        · cases' k_cases with hk hk
          · subst hi hj hk; contradiction
          · subst hi hj hk; contradiction
          · subst hi hj hk
            simp [List.get!] at h_sum
            left; exact h_sum
        · subst hi hj; contradiction
        · cases' k_cases with hk hk
          · subst hi hj hk
            simp [List.get!] at h_sum
            right; right; exact h_sum
          · subst hi hj hk; contradiction
          · subst hi hj hk; contradiction
      · cases' j_cases with hj hj
        · cases' k_cases with hk hk
          · subst hi hj hk; contradiction
          · subst hi hj hk
            simp [List.get!] at h_sum
            right; left; exact h_sum
          · subst hi hj hk; contradiction
        · cases' k_cases with hk hk
          · subst hi hj hk
            simp [List.get!] at h_sum
            right; right; exact h_sum
          · subst hi hj hk; contradiction
          · subst hi hj hk; contradiction
        · subst hi hj; contradiction
  · intro h
    cases' h with h h
    · exact ⟨0, 1, 2, by simp, by norm_num, by norm_num, by norm_num, by simp [List.get!, h]⟩
    · cases' h with h h
      · exact ⟨0, 2, 1, by simp, by norm_num, by norm_num, by norm_num, by simp [List.get!, h]⟩
      · exact ⟨1, 2, 0, by simp, by norm_num, by norm_num, by norm_num, by simp [List.get!, h]⟩

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  simp [problem_spec]
  use implementation a b c
  constructor
  · rfl
  · simp [implementation, is_integer, check_sum_condition]
    constructor
    · intro ⟨h_a, h_b, h_c, h_sum⟩
      constructor
      · rw [← exists_indices_iff]
        exact h_sum
      · exact ⟨h_a, h_b, h_c⟩
    · intro ⟨h_exists, h_a, h_b, h_c⟩
      constructor
      · exact h_a
      · constructor
        · exact h_b
        · constructor
          · exact h_c
          · rw [exists_indices_iff] at h_exists
            exact h_exists