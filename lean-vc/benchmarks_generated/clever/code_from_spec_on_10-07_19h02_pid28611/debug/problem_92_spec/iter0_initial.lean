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
def check_triple_sum (a b c : Rat) : Bool :=
  (a + b = c) ∨ (a + c = b) ∨ (b + c = a)

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool := 
  is_integer a ∧ is_integer b ∧ is_integer c ∧ check_triple_sum a b c

-- LLM HELPER
lemma triple_indices_exist (a b c : Rat) : 
  ((a + b = c) ∨ (a + c = b) ∨ (b + c = a)) ↔ 
  ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ ([a, b, c][i]! + [a, b, c][j]! = [a, b, c][k]!) := by
  constructor
  · intro h
    cases' h with h h
    · -- a + b = c, so indices 0, 1, 2
      use 0, 1, 2
      constructor
      · simp [Set.subset_def]
      constructor
      · norm_num
      constructor  
      · norm_num
      constructor
      · norm_num
      · simp [List.getElem_fin]
        exact h
    cases' h with h h
    · -- a + c = b, so indices 0, 2, 1
      use 0, 2, 1
      constructor
      · simp [Set.subset_def]
      constructor
      · norm_num
      constructor
      · norm_num  
      constructor
      · norm_num
      · simp [List.getElem_fin]
        exact h
    · -- b + c = a, so indices 1, 2, 0
      use 1, 2, 0
      constructor
      · simp [Set.subset_def]
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · simp [List.getElem_fin]
        exact h
  · intro ⟨i, j, k, h_sub, h_ij, h_jk, h_ki, h_sum⟩
    -- Need to consider all possible values of i, j, k
    have h_vals : i ∈ ({0, 1, 2} : Set ℕ) ∧ j ∈ ({0, 1, 2} : Set ℕ) ∧ k ∈ ({0, 1, 2} : Set ℕ) := by
      simp [Set.subset_def] at h_sub
      exact ⟨h_sub i (by simp), h_sub j (by simp), h_sub k (by simp)⟩
    interval_cases i <;> interval_cases j <;> interval_cases k <;> 
    (first | contradiction | (simp [List.getElem_fin] at h_sum; tauto))

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  unfold problem_spec implementation is_integer check_triple_sum
  use (a.den = 1 ∧ b.den = 1 ∧ c.den = 1 ∧ ((a + b = c) ∨ (a + c = b) ∨ (b + c = a)))
  constructor
  · rfl
  · constructor
    · intro h
      rw [triple_indices_exist]
      tauto
    · intro ⟨i, j, k, h_sub, h_ij, h_jk, h_ki, h_sum, h_a, h_b, h_c⟩
      constructor
      · exact h_a
      constructor
      · exact h_b  
      constructor
      · exact h_c
      · rw [← triple_indices_exist]
        exact h_sum