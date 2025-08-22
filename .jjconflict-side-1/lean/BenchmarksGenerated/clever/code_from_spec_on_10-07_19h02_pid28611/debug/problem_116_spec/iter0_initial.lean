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
def sort_by_binary_then_value (lst : List Nat) : List Nat :=
  lst.mergeSort (fun a b => 
    let bin_a := binary_length a
    let bin_b := binary_length b
    bin_a < bin_b ∨ (bin_a = bin_b ∧ a < b))

-- LLM HELPER
lemma mergeSort_count (lst : List Nat) (x : Nat) : 
  lst.count x = (lst.mergeSort (fun a b => 
    let bin_a := binary_length a
    let bin_b := binary_length b
    bin_a < bin_b ∨ (bin_a = bin_b ∧ a < b))).count x := by
  exact List.count_mergeSort _ _

-- LLM HELPER
lemma mergeSort_length (lst : List Nat) : 
  lst.length = (lst.mergeSort (fun a b => 
    let bin_a := binary_length a
    let bin_b := binary_length b
    bin_a < bin_b ∨ (bin_a = bin_b ∧ a < b))).length := by
  exact List.length_mergeSort _ _

-- LLM HELPER
lemma binary_length_eq_digits_length (n : Nat) : binary_length n = (Nat.digits 2 n).length := by
  rfl

-- LLM HELPER
lemma mergeSort_sorted (lst : List Nat) :
  let sorted := lst.mergeSort (fun a b => 
    let bin_a := binary_length a
    let bin_b := binary_length b
    bin_a < bin_b ∨ (bin_a = bin_b ∧ a < b))
  ∀ i j : Nat, i < j → j < sorted.length →
    Nat.digits 2 (sorted.get! i) < Nat.digits 2 (sorted.get! j) ∨
    (Nat.digits 2 (sorted.get! i) = Nat.digits 2 (sorted.get! j) ∧ sorted.get! i < sorted.get! j) := by
  intro sorted i j hij hjlen
  have h_sorted := List.mergeSort_sorted (fun a b => 
    let bin_a := binary_length a
    let bin_b := binary_length b
    bin_a < bin_b ∨ (bin_a = bin_b ∧ a < b)) lst
  have h_trans : Transitive (fun a b => 
    let bin_a := binary_length a
    let bin_b := binary_length b
    bin_a < bin_b ∨ (bin_a = bin_b ∧ a < b)) := by
    intro a b c hab hbc
    simp [binary_length] at hab hbc ⊢
    cases' hab with h1 h1
    · cases' hbc with h2 h2
      · left; exact Nat.lt_trans h1 h2
      · left; rw [← h2.1]; exact h1
    · cases' hbc with h2 h2
      · left; rw [h1.1]; exact h2
      · right; exact ⟨Nat.eq_trans h1.1 h2.1, Nat.lt_trans h1.2 h2.2⟩
  have h_total : Total (fun a b => 
    let bin_a := binary_length a
    let bin_b := binary_length b
    bin_a < bin_b ∨ (bin_a = bin_b ∧ a < b)) := by
    intro a b
    simp [binary_length]
    by_cases h : (Nat.digits 2 a).length < (Nat.digits 2 b).length
    · left; left; exact h
    · by_cases h2 : (Nat.digits 2 a).length = (Nat.digits 2 b).length
      · by_cases h3 : a < b
        · left; right; exact ⟨h2, h3⟩
        · right
          by_cases h4 : a = b
          · rw [h4]
            right; exact ⟨h2.symm, Nat.lt_refl _⟩
          · left
            have : b < a := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h3) (Ne.symm h4)
            right; exact ⟨h2.symm, this⟩
      · right; left
        have : (Nat.digits 2 b).length < (Nat.digits 2 a).length := by
          exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm h2)
        exact this
  have := List.pairwise_of_sorted h_sorted h_trans h_total
  simp [List.Pairwise] at this
  have h_get := List.get_mem sorted ⟨i, by rwa [List.length_mergeSort] at hjlen⟩
  have h_get2 := List.get_mem sorted ⟨j, hjlen⟩
  rw [← List.get_get!] at h_get h_get2
  simp [binary_length_eq_digits_length]
  apply this i j hij

def implementation (lst: List Nat) : List Nat := sort_by_binary_then_value lst

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  simp [problem_spec, implementation, sort_by_binary_then_value]
  use lst.mergeSort (fun a b => 
    let bin_a := binary_length a
    let bin_b := binary_length b
    bin_a < bin_b ∨ (bin_a = bin_b ∧ a < b))
  constructor
  · rfl
  · constructor
    · intro x
      rw [← mergeSort_count]
    · constructor
      · rw [← mergeSort_length]
      · exact mergeSort_sorted lst