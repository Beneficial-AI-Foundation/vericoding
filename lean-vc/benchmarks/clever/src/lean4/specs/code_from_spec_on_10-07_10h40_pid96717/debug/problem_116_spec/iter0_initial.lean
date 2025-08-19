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
def bitLength (n : Nat) : Nat := (Nat.digits 2 n).length

-- LLM HELPER
def compareByBits (a b : Nat) : Bool :=
  let bitsA := Nat.digits 2 a
  let bitsB := Nat.digits 2 b
  if bitsA.length < bitsB.length then true
  else if bitsA.length > bitsB.length then false
  else a < b

def implementation (lst: List Nat) : List Nat := 
  lst.mergeSort compareByBits

-- LLM HELPER
lemma mergeSort_length {α : Type*} (r : α → α → Bool) (l : List α) : 
  (l.mergeSort r).length = l.length := by
  exact List.length_mergeSort l

-- LLM HELPER
lemma mergeSort_count {α : Type*} [DecidableEq α] (r : α → α → Bool) (l : List α) (x : α) : 
  (l.mergeSort r).count x = l.count x := by
  exact List.count_mergeSort r l x

-- LLM HELPER
lemma mergeSort_sorted {α : Type*} (r : α → α → Bool) [DecidableRel r] (l : List α) :
  (l.mergeSort r).Sorted r := by
  exact List.sorted_mergeSort r l

-- LLM HELPER
lemma compareByBits_transitive : ∀ a b c : Nat, compareByBits a b = true → compareByBits b c = true → compareByBits a c = true := by
  intro a b c hab hbc
  unfold compareByBits at hab hbc ⊢
  simp at hab hbc ⊢
  by_cases h1 : (Nat.digits 2 a).length < (Nat.digits 2 b).length
  · simp [h1] at hab
    by_cases h2 : (Nat.digits 2 b).length < (Nat.digits 2 c).length
    · simp [h2] at hbc
      simp [Nat.lt_trans h1 h2]
    · simp [h2] at hbc
      by_cases h3 : (Nat.digits 2 b).length > (Nat.digits 2 c).length
      · simp [h3] at hbc
      · simp [h3] at hbc
        have : (Nat.digits 2 b).length = (Nat.digits 2 c).length := by
          exact Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h3) (Nat.lt_succ_of_not_le h2)
        rw [this] at h1
        simp [h1]
  · simp [h1] at hab
    by_cases h2 : (Nat.digits 2 a).length > (Nat.digits 2 b).length
    · simp [h2] at hab
    · simp [h2] at hab
      have hab_eq : (Nat.digits 2 a).length = (Nat.digits 2 b).length := by
        exact Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h2) (Nat.lt_succ_of_not_le h1)
      by_cases h3 : (Nat.digits 2 b).length < (Nat.digits 2 c).length
      · simp [h3] at hbc
        rw [hab_eq] at h3
        simp [h3]
      · simp [h3] at hbc
        by_cases h4 : (Nat.digits 2 b).length > (Nat.digits 2 c).length
        · simp [h4] at hbc
        · simp [h4] at hbc
          have hbc_eq : (Nat.digits 2 b).length = (Nat.digits 2 c).length := by
            exact Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h4) (Nat.lt_succ_of_not_le h3)
          rw [hab_eq, hbc_eq]
          simp
          exact Nat.lt_trans hab hbc

-- LLM HELPER
lemma compareByBits_irrefl : ∀ a : Nat, compareByBits a a = false := by
  intro a
  unfold compareByBits
  simp

-- LLM HELPER
lemma compareByBits_total : ∀ a b : Nat, compareByBits a b = true ∨ compareByBits b a = true ∨ a = b := by
  intro a b
  unfold compareByBits
  by_cases h : (Nat.digits 2 a).length < (Nat.digits 2 b).length
  · simp [h]
  · simp [h]
    by_cases h' : (Nat.digits 2 a).length > (Nat.digits 2 b).length
    · simp [h']
      right
      left
      simp [Nat.lt_of_le_of_ne (Nat.le_of_not_gt h') (Ne.symm (Nat.ne_of_gt h'))]
    · simp [h']
      have : (Nat.digits 2 a).length = (Nat.digits 2 b).length := by
        exact Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h') (Nat.lt_succ_of_not_le h)
      by_cases h'' : a < b
      · simp [h'']
      · simp [h'']
        by_cases h''' : b < a
        · right
          left
          simp [this.symm, h''']
        · right
          right
          exact Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h''') (Nat.lt_succ_of_not_le h'')

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  simp
  let result := lst.mergeSort compareByBits
  use result
  constructor
  · rfl
  · intro x
    constructor
    · exact mergeSort_count compareByBits lst x
    · constructor
      · exact mergeSort_length compareByBits lst
      · intro i j hij hjlen
        have sorted := mergeSort_sorted compareByBits lst
        have : i < result.length := Nat.lt_trans hij hjlen
        have : compareByBits (result.get! i) (result.get! j) = true := by
          apply List.Sorted.get_lt_get sorted
          · exact this
          · exact hjlen
          · exact hij
        unfold compareByBits at this
        simp at this
        by_cases h : (Nat.digits 2 (result.get! i)).length < (Nat.digits 2 (result.get! j)).length
        · simp [h] at this
          left
          exact h
        · simp [h] at this
          by_cases h' : (Nat.digits 2 (result.get! i)).length > (Nat.digits 2 (result.get! j)).length
          · simp [h'] at this
          · simp [h'] at this
            right
            constructor
            · have : (Nat.digits 2 (result.get! i)).length = (Nat.digits 2 (result.get! j)).length := by
                exact Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h') (Nat.lt_succ_of_not_le h)
              rw [List.length_eq_iff_eq_nil_or_exists_mem_and_length] at this
              exact this
            · exact this