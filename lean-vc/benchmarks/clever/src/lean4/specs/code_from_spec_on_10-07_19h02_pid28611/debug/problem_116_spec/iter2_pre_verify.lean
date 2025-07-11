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
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  ∀ x : Nat, lst.count x = result.count x ∧
  result.length = lst.length ∧
  (∀ i j : Nat, i < j → j < result.length →
    Nat.digits 2 (result.get! i) < Nat.digits 2 (result.get! j) ∨
    (Nat.digits 2 (result.get! i) = Nat.digits 2 (result.get! j) ∧ result.get! i < result.get! j))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def binary_length (n : Nat) : Nat := (Nat.digits 2 n).length

-- LLM HELPER
def compare_binary_then_value (a b : Nat) : Bool :=
  let bin_a := binary_length a
  let bin_b := binary_length b
  decide (bin_a < bin_b) || (decide (bin_a = bin_b) && decide (a < b))

-- LLM HELPER
lemma mergeSort_count (lst : List Nat) (x : Nat) : 
  lst.count x = (lst.mergeSort compare_binary_then_value).count x := by
  exact List.count_mergeSort _ _

-- LLM HELPER
lemma mergeSort_length (lst : List Nat) : 
  lst.length = (lst.mergeSort compare_binary_then_value).length := by
  exact List.length_mergeSort _ _

-- LLM HELPER
lemma binary_length_eq_digits_length (n : Nat) : binary_length n = (Nat.digits 2 n).length := by
  rfl

-- LLM HELPER
lemma compare_binary_then_value_trans : Transitive compare_binary_then_value := by
  intro a b c hab hbc
  simp [compare_binary_then_value] at hab hbc ⊢
  cases' hab with h1 h1
  · cases' h1 with h11 h12
    · cases' hbc with h2 h2
      · cases' h2 with h21 h22
        · left; left; exact Nat.lt_trans h11 h21
        · left; left; rw [← h21]; exact h11
      · cases' h2 with h21 h22
        · left; left; rw [h21]; exact h11
        · left; left; rw [h21]; exact h11
    · cases' hbc with h2 h2
      · cases' h2 with h21 h22
        · left; left; rw [h12]; exact h21
        · left; left; rw [h12, h21]
      · cases' h2 with h21 h22
        · left; left; rw [h12]; exact h21
        · right; exact ⟨Nat.eq_trans h12 h21, Nat.lt_trans h1 h22⟩
  · cases' hbc with h2 h2
    · cases' h2 with h21 h22
      · left; left; rw [← h1]; exact h21
      · left; left; rw [← h1, h21]
    · cases' h2 with h21 h22
      · left; left; rw [← h1]; exact h21
      · right; exact ⟨Nat.eq_trans h1 h21, Nat.lt_trans hab h2⟩

-- LLM HELPER
lemma compare_binary_then_value_total : Total compare_binary_then_value := by
  intro a b
  simp [compare_binary_then_value, binary_length]
  by_cases h : (Nat.digits 2 a).length < (Nat.digits 2 b).length
  · left; left; exact h
  · by_cases h2 : (Nat.digits 2 a).length = (Nat.digits 2 b).length
    · by_cases h3 : a < b
      · left; right; exact ⟨h2, h3⟩
      · right; left
        have : (Nat.digits 2 b).length < (Nat.digits 2 a).length ∨ 
               ((Nat.digits 2 b).length = (Nat.digits 2 a).length ∧ b < a) := by
          right
          constructor
          · exact h2.symm
          · by_cases h4 : a = b
            · rw [h4] at h3
              exact absurd (Nat.lt_refl b) h3
            · exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt h3) (Ne.symm h4)
        exact this
    · right; left
      have : (Nat.digits 2 b).length < (Nat.digits 2 a).length := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm h2)
      left; exact this

-- LLM HELPER
lemma mergeSort_sorted (lst : List Nat) :
  let sorted := lst.mergeSort compare_binary_then_value
  ∀ i j : Nat, i < j → j < sorted.length →
    Nat.digits 2 (sorted.get! i) < Nat.digits 2 (sorted.get! j) ∨
    (Nat.digits 2 (sorted.get! i) = Nat.digits 2 (sorted.get! j) ∧ sorted.get! i < sorted.get! j) := by
  intro sorted i j hij hjlen
  have h_sorted := List.sorted_mergeSort compare_binary_then_value lst
  have h_pairwise := List.pairwise_of_sorted h_sorted compare_binary_then_value_trans compare_binary_then_value_total
  simp [List.Pairwise] at h_pairwise
  have h_rel := h_pairwise i j hij
  simp [compare_binary_then_value, binary_length_eq_digits_length] at h_rel
  cases' h_rel with h1 h1
  · cases' h1 with h11 h12
    · left; exact h11
    · right; exact h12
  · cases' h1 with h11 h12
    · left; exact h11
    · right; exact ⟨h11, h12⟩

def implementation (lst: List Nat) : List Nat := 
  lst.mergeSort compare_binary_then_value

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  simp [problem_spec, implementation]
  use lst.mergeSort compare_binary_then_value
  constructor
  · rfl
  · constructor
    · intro x
      exact (mergeSort_count lst x).symm
    · constructor
      · exact (mergeSort_length lst).symm
      · exact mergeSort_sorted lst