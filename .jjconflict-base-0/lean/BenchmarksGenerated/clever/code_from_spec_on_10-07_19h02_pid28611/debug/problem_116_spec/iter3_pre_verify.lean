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
  exact List.count_mergeSort

-- LLM HELPER
lemma mergeSort_length (lst : List Nat) : 
  lst.length = (lst.mergeSort compare_binary_then_value).length := by
  exact List.length_mergeSort

-- LLM HELPER
lemma binary_length_eq_digits_length (n : Nat) : binary_length n = (Nat.digits 2 n).length := by
  rfl

-- LLM HELPER
def compare_rel (a b : Nat) : Prop :=
  binary_length a < binary_length b ∨ (binary_length a = binary_length b ∧ a < b)

-- LLM HELPER
lemma compare_binary_then_value_iff (a b : Nat) : 
  compare_binary_then_value a b = true ↔ compare_rel a b := by
  simp [compare_binary_then_value, compare_rel, binary_length]
  constructor
  · intro h
    cases' h with h1 h1
    · left; exact h1
    · right; exact h1
  · intro h
    cases' h with h1 h1
    · left; exact h1
    · right; exact h1

-- LLM HELPER
lemma compare_rel_trans : Transitive compare_rel := by
  intro a b c hab hbc
  simp [compare_rel] at hab hbc ⊢
  cases' hab with h1 h1
  · cases' hbc with h2 h2
    · left; exact Nat.lt_trans h1 h2
    · left; rw [← h2.1]; exact h1
  · cases' hbc with h2 h2
    · left; rw [h1.1]; exact h2
    · right; exact ⟨Nat.eq_trans h1.1 h2.1, Nat.lt_trans h1.2 h2.2⟩

-- LLM HELPER
lemma compare_rel_total : Total compare_rel := by
  intro a b
  simp [compare_rel, binary_length]
  by_cases h : (Nat.digits 2 a).length < (Nat.digits 2 b).length
  · left; left; exact h
  · by_cases h2 : (Nat.digits 2 a).length = (Nat.digits 2 b).length
    · by_cases h3 : a < b
      · left; right; exact ⟨h2, h3⟩
      · right; 
        by_cases h4 : a = b
        · rw [h4]; left; right; exact ⟨h2.symm, Nat.lt_refl b⟩
        · left; right; exact ⟨h2.symm, Nat.lt_of_le_of_ne (Nat.le_of_not_lt h3) (Ne.symm h4)⟩
    · right; left
      have : (Nat.digits 2 b).length < (Nat.digits 2 a).length := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm h2)
      exact this

-- LLM HELPER
lemma mergeSort_sorted (lst : List Nat) :
  let sorted := lst.mergeSort compare_binary_then_value
  ∀ i j : Nat, i < j → j < sorted.length →
    Nat.digits 2 (sorted.get! i) < Nat.digits 2 (sorted.get! j) ∨
    (Nat.digits 2 (sorted.get! i) = Nat.digits 2 (sorted.get! j) ∧ sorted.get! i < sorted.get! j) := by
  intro sorted i j hij hjlen
  have h_sorted := List.sorted_mergeSort compare_binary_then_value lst
  have h_pairwise : List.Pairwise (fun a b => compare_binary_then_value a b = true) sorted := by
    exact List.pairwise_of_sorted h_sorted
  have h_rel : compare_binary_then_value (sorted.get! i) (sorted.get! j) = true := by
    have h_get_i : i < sorted.length := Nat.lt_trans hij hjlen
    have h_get_j : j < sorted.length := hjlen
    exact List.pairwise_get h_pairwise hij
  rw [compare_binary_then_value_iff] at h_rel
  simp [compare_rel, binary_length_eq_digits_length] at h_rel
  exact h_rel

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
      constructor
      · exact (mergeSort_count lst x).symm
      · constructor
        · exact (mergeSort_length lst).symm
        · exact mergeSort_sorted lst
    · constructor
      · exact (mergeSort_length lst).symm
      · exact mergeSort_sorted lst