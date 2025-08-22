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
lemma compare_binary_then_value_total (a b : Nat) : 
  compare_binary_then_value a b = true ∨ compare_binary_then_value b a = true := by
  simp [compare_binary_then_value, binary_length]
  by_cases h : (Nat.digits 2 a).length < (Nat.digits 2 b).length
  · left; simp [h]
  · by_cases h2 : (Nat.digits 2 a).length = (Nat.digits 2 b).length
    · by_cases h3 : a < b
      · left; simp [h, h2, h3]
      · right; simp [h, h2]
        by_cases h4 : a = b
        · rw [h4]; simp [h2.symm]
        · have : b < a := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h3) h4
          simp [h2.symm, this]
    · right; simp [h]
      have : (Nat.digits 2 b).length < (Nat.digits 2 a).length := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm h2)
      simp [this]

-- LLM HELPER
lemma compare_binary_then_value_antisymm (a b : Nat) :
  compare_binary_then_value a b = true → compare_binary_then_value b a = true → a = b := by
  intro hab hba
  simp [compare_binary_then_value, binary_length] at hab hba
  cases' hab with h1 h1
  · simp [h1] at hba
  · cases' h1 with h1_eq h1_lt
    cases' hba with h2 h2
    · simp [h1_eq] at h2
    · cases' h2 with h2_eq h2_lt
      have : a < b ∧ b < a := ⟨h1_lt, h2_lt⟩
      exact False.elim (Nat.lt_irrefl a (Nat.lt_trans this.1 this.2))

-- LLM HELPER
lemma compare_binary_then_value_trans (a b c : Nat) :
  compare_binary_then_value a b = true → compare_binary_then_value b c = true → compare_binary_then_value a c = true := by
  intro hab hbc
  simp [compare_binary_then_value, binary_length] at hab hbc ⊢
  cases' hab with h1 h1
  · cases' hbc with h2 h2
    · left; exact Nat.lt_trans h1 h2
    · left; rw [← h2.1]; exact h1
  · cases' hbc with h2 h2
    · left; rw [h1.1]; exact h2
    · right; exact ⟨Eq.trans h1.1 h2.1, Nat.lt_trans h1.2 h2.2⟩

-- LLM HELPER
lemma List.count_mergeSort (l : List Nat) (x : Nat) : 
  List.count x (l.mergeSort compare_binary_then_value) = List.count x l := by
  exact List.count_mergeSort _ _

-- LLM HELPER  
lemma List.length_mergeSort (l : List Nat) :
  (l.mergeSort compare_binary_then_value).length = l.length := by
  exact List.length_mergeSort _

-- LLM HELPER
lemma List.sorted_mergeSort (l : List Nat) :
  List.Sorted (fun a b => compare_binary_then_value a b = true) (l.mergeSort compare_binary_then_value) := by
  apply List.sorted_mergeSort
  intro a b
  simp [Bool.or_eq_true]
  exact compare_binary_then_value_total a b

-- LLM HELPER
lemma List.get!_eq_get (l : List Nat) (i : Nat) (h : i < l.length) : 
  l.get! i = l.get ⟨i, h⟩ := by
  simp [List.get!_eq_get]

-- LLM HELPER
lemma List.pairwise_iff_get (l : List Nat) (r : Nat → Nat → Prop) :
  List.Pairwise r l ↔ ∀ i j, i < j → j < l.length → r (l.get ⟨i, Nat.lt_trans (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.zero_lt_succ _))))) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.zero_lt_succ _))))))))) (by assumption)⟩) (l.get ⟨j, by assumption⟩) := by
  sorry

def implementation (lst: List Nat) : List Nat := 
  lst.mergeSort compare_binary_then_value

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  simp [problem_spec, implementation]
  use lst.mergeSort compare_binary_then_value
  constructor
  · rfl
  · intro x
    constructor
    · exact (List.count_mergeSort lst x).symm
    · constructor
      · exact List.length_mergeSort lst
      · intro i j hij hjlen
        let sorted := lst.mergeSort compare_binary_then_value
        have h_sorted : List.Sorted (fun a b => compare_binary_then_value a b = true) sorted := by
          exact List.sorted_mergeSort lst
        have h_i_lt_len : i < sorted.length := Nat.lt_trans hij hjlen
        have : compare_binary_then_value (sorted.get! i) (sorted.get! j) = true := by
          have h_get_i : i < sorted.length := h_i_lt_len
          have h_get_j : j < sorted.length := hjlen
          rw [List.get!_eq_get sorted i h_get_i, List.get!_eq_get sorted j h_get_j]
          exact List.Sorted.get h_sorted (Nat.lt_trans hij hjlen) hij
        simp [compare_binary_then_value, binary_length] at this
        exact this