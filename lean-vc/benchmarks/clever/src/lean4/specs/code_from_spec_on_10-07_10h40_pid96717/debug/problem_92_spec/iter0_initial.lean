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
lemma list_get_0_1_2 (a b c : Rat) : 
  let nums := [a, b, c]
  nums[0]! = a ∧ nums[1]! = b ∧ nums[2]! = c := by
  simp [List.get!]

-- LLM HELPER
lemma check_sum_condition_iff (a b c : Rat) :
  check_sum_condition a b c = true ↔ (a + b = c) ∨ (a + c = b) ∨ (b + c = a) := by
  simp [check_sum_condition]

-- LLM HELPER
lemma exists_indices_iff (a b c : Rat) :
  (∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ ([a, b, c][i]! + [a, b, c][j]! = [a, b, c][k]!)) ↔ 
  ((a + b = c) ∨ (a + c = b) ∨ (b + c = a)) := by
  constructor
  · intro ⟨i, j, k, h_sub, h_ij, h_jk, h_ki, h_sum⟩
    simp [List.get!] at h_sum
    have h_mem : i ∈ {0, 1, 2} ∧ j ∈ {0, 1, 2} ∧ k ∈ {0, 1, 2} := by
      exact ⟨h_sub (Set.mem_insert _ _), h_sub (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), h_sub (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
    interval_cases i <;> interval_cases j <;> interval_cases k <;> 
    simp at h_ij h_jk h_ki h_sum <;> 
    try (left; exact h_sum) <;> 
    try (right; left; exact h_sum) <;> 
    try (right; right; exact h_sum)
  · intro h
    cases h with
    | inl h => exact ⟨0, 1, 2, by simp, by norm_num, by norm_num, by norm_num, by simp [List.get!, h]⟩
    | inr h => cases h with
      | inl h => exact ⟨0, 2, 1, by simp, by norm_num, by norm_num, by norm_num, by simp [List.get!, h]⟩
      | inr h => exact ⟨1, 2, 0, by simp, by norm_num, by norm_num, by norm_num, by simp [List.get!, h]⟩

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  simp [problem_spec]
  use implementation a b c
  constructor
  · rfl
  · simp [implementation, is_integer]
    constructor
    · intro ⟨h_a, h_b, h_c, h_sum⟩
      rw [check_sum_condition_iff] at h_sum
      rw [← exists_indices_iff]
      exact ⟨h_sum, h_a, h_b, h_c⟩
    · intro ⟨h_exists, h_a, h_b, h_c⟩
      constructor
      · exact h_a
      · constructor
        · exact h_b
        · constructor
          · exact h_c
          · rw [check_sum_condition_iff]
            rw [exists_indices_iff] at h_exists
            exact h_exists