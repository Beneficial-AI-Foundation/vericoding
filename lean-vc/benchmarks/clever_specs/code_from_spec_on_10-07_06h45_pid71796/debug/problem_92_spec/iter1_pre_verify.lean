import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
def isInteger (r : Rat) : Bool := r.den = 1

-- LLM HELPER
def checkTripleSumProperty (a b c : Rat) : Bool :=
  (a + b = c) ∨ (a + c = b) ∨ (b + c = a)

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool := 
  isInteger a ∧ isInteger b ∧ isInteger c ∧ checkTripleSumProperty a b c

-- LLM HELPER
lemma three_distinct_indices : ∀ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i → 
  ({i, j, k} = {0, 1, 2}) := by
  intro i j k h
  have hi : i ∈ ({0, 1, 2} : Set ℕ) := h.1 (Set.mem_insert _ _)
  have hj : j ∈ ({0, 1, 2} : Set ℕ) := h.1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hk : k ∈ ({0, 1, 2} : Set ℕ) := h.1 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have card_ijk : {i, j, k}.ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨i, j, k, h.2.1, h.2.2.1, h.2.2.2, rfl⟩
  have card_012 : ({0, 1, 2} : Set ℕ).ncard = 3 := by simp [Set.ncard_insert_of_not_mem]
  have sub : {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) := h.1
  have eq_card : {i, j, k}.ncard = ({0, 1, 2} : Set ℕ).ncard := by rw [card_ijk, card_012]
  exact Set.eq_of_subset_of_ncard_eq sub eq_card

-- LLM HELPER
lemma list_get_cases (a b c : Rat) (i : ℕ) (h : i < 3) : 
  [a, b, c][i]! = if i = 0 then a else if i = 1 then b else c := by
  fin_cases i <;> simp

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  simp [problem_spec, implementation, isInteger, checkTripleSumProperty]
  constructor
  · intro h
    constructor
    · intro h_true
      cases' h_true with h_int h_sum
      cases' h_int with h_a h_rest
      cases' h_rest with h_b h_c
      cases' h_sum with h1 h_sum
      · -- case a + b = c
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
        · simp [List.get_eq_getElem, h1]
        exact ⟨h_a, h_b, h_c⟩
      cases' h_sum with h2 h3
      · -- case a + c = b  
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
        · simp [List.get_eq_getElem, h2]
        exact ⟨h_a, h_b, h_c⟩
      · -- case b + c = a
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
        · simp [List.get_eq_getElem, h3]
        exact ⟨h_a, h_b, h_c⟩
    · intro h_exists
      cases' h_exists with i h_i
      cases' h_i with j h_j
      cases' h_j with k h_k
      have h_eq := three_distinct_indices i j k h_k
      have h_ijk : {i, j, k} = {0, 1, 2} := h_eq
      constructor
      · exact h_k.2.2.2.2.1
      constructor  
      · rw [h_k.2.2.2.2.2.1]; exact h_k.2.2.2.2.2.2
      constructor
      · rw [h_k.2.2.2.2.2.1]; exact h_k.2.2.2.2.2.2
      -- Now we need to show one of the sum conditions
      have sum_eq : [a, b, c][i]! + [a, b, c][j]! = [a, b, c][k]! := h_k.2.2.2.1
      -- Since {i,j,k} = {0,1,2} and all are distinct, we have three cases
      have hi_mem : i ∈ ({0, 1, 2} : Set ℕ) := by rw [← h_ijk]; exact Set.mem_insert i {j, k}
      have hj_mem : j ∈ ({0, 1, 2} : Set ℕ) := by rw [← h_ijk]; exact Set.mem_insert_of_mem i (Set.mem_insert j {k})
      have hk_mem : k ∈ ({0, 1, 2} : Set ℕ) := by rw [← h_ijk]; exact Set.mem_insert_of_mem i (Set.mem_insert_of_mem j (Set.mem_singleton k))
      interval_cases i <;> interval_cases j <;> interval_cases k <;> 
      (try simp at h_k.2.1 h_k.2.2.1 h_k.2.2.2) <;>
      (try (left; simp [List.get_eq_getElem] at sum_eq; exact sum_eq)) <;>
      (try (right; left; simp [List.get_eq_getElem] at sum_eq; exact sum_eq)) <;>
      (try (right; right; simp [List.get_eq_getElem] at sum_eq; exact sum_eq))
  · rfl