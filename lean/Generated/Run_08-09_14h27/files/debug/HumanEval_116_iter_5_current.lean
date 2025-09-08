import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_ones (n : Nat) : Nat :=
  (Nat.digits 2 n).count 1

-- LLM HELPER
def compare_by_ones_then_value (a b : Nat) : Bool :=
  let ones_a := count_ones a
  let ones_b := count_ones b
  if ones_a < ones_b then true
  else if ones_a > ones_b then false
  else a < b

def implementation (lst: List Nat) : List Nat :=
  lst.mergeSort compare_by_ones_then_value

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
    (Nat.digits 2 (result[i]!)).count 1 < (Nat.digits 2 (result[j]!)).count 1 ∨
    ((Nat.digits 2 (result[i]!)).count 1 = (Nat.digits 2 (result[j]!)).count 1 ∧ result[i]! < result[j]!))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
lemma mergeSort_count (lst : List Nat) (cmp : Nat → Nat → Bool) (x : Nat) :
  (lst.mergeSort cmp).count x = lst.count x := by
  exact List.count_mergeSort lst x

-- LLM HELPER
lemma mergeSort_length (lst : List Nat) (cmp : Nat → Nat → Bool) :
  (lst.mergeSort cmp).length = lst.length := by
  exact List.length_mergeSort cmp lst

-- LLM HELPER
lemma compare_total : ∀ a b : Nat, compare_by_ones_then_value a b ∨ compare_by_ones_then_value b a := by
  intros a b
  unfold compare_by_ones_then_value
  by_cases h : count_ones a < count_ones b
  · left; simp [h]
  · by_cases h' : count_ones a > count_ones b
    · right; simp [h']
    · simp [Nat.not_lt] at h h'
      have : count_ones a = count_ones b := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h') (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))
      simp [this]
      by_cases h_ab : a < b
      · left; exact h_ab
      · right; simp [Nat.not_lt] at h_ab
        exact Nat.lt_of_le_of_ne h_ab (Ne.symm (Nat.ne_of_not_lt h_ab))

-- LLM HELPER
lemma compare_antisymm : ∀ a b : Nat, compare_by_ones_then_value a b → ¬compare_by_ones_then_value b a := by
  intros a b hab
  unfold compare_by_ones_then_value at *
  by_cases h1 : count_ones a < count_ones b
  · simp [h1] at hab
    simp [Nat.not_lt.mpr (Nat.le_of_lt h1)]
  · by_cases h2 : count_ones a > count_ones b
    · simp [h1, h2] at hab
    · simp [h1, h2] at hab
      simp [Nat.not_lt] at h1 h2
      have : count_ones a = count_ones b := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h2) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h1))
      simp [this, Nat.not_lt.mpr (Nat.le_of_lt hab)]

-- LLM HELPER
lemma compare_trans : ∀ a b c : Nat, 
  compare_by_ones_then_value a b → compare_by_ones_then_value b c → compare_by_ones_then_value a c := by
  intros a b c hab hbc
  unfold compare_by_ones_then_value at *
  by_cases h1 : count_ones a < count_ones b
  · simp [h1] at hab
    by_cases h2 : count_ones b < count_ones c
    · simp [h2] at hbc
      simp [Nat.lt_trans h1 h2]
    · by_cases h3 : count_ones b > count_ones c
      · simp [h2, h3] at hbc
      · simp [Nat.not_lt] at h2 h3
        have : count_ones b = count_ones c := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h3) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h2))
        rw [this] at h1
        simp [h1]
  · by_cases h4 : count_ones a > count_ones b
    · simp [h1, h4] at hab
    · simp [h1, h4] at hab
      simp [Nat.not_lt] at h1 h4
      have h_eq : count_ones a = count_ones b := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h4) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h1))
      by_cases h2 : count_ones b < count_ones c
      · simp [h2] at hbc
        rw [h_eq]
        simp [h2]
      · by_cases h3 : count_ones b > count_ones c
        · simp [h2, h3] at hbc
        · simp [h2, h3] at hbc
          simp [Nat.not_lt] at h2 h3
          have h_eq2 : count_ones b = count_ones c := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h3) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h2))
          rw [h_eq, h_eq2]
          simp
          exact Nat.lt_trans hab hbc

-- LLM HELPER
lemma sort_property (lst : List Nat) (i j : Nat) (hi : i < j) 
  (hj : j < (lst.mergeSort compare_by_ones_then_value).length) :
  count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) < count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) ∨
  (count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) = count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) ∧ 
   (lst.mergeSort compare_by_ones_then_value)[i]! < (lst.mergeSort compare_by_ones_then_value)[j]!) := by
  have sorted := List.sorted_mergeSort compare_trans lst
  have hi_bound : i < (lst.mergeSort compare_by_ones_then_value).length := Nat.lt_trans hi hj
  have h_relation := List.pairwise_of_sorted sorted i j hi_bound hj hi
  unfold compare_by_ones_then_value at h_relation
  simp at h_relation
  by_cases h1 : count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) < count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!)
  · left; exact h1
  · right
    simp [Nat.not_lt] at h1
    by_cases h2 : count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) > count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!)
    · exfalso
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h1 h2)
    · simp [Nat.not_lt] at h2
      have h_eq : count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) = count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) := 
        Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h2) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h1))
      constructor
      · exact h_eq
      · cases' Nat.lt_trichotomy (count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!)) (count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!)) with h_case h_other
        · contradiction
        · cases h_other with
          | inl h_eq_case => exact h_relation h_eq_case
          | inr h_gt => contradiction

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  use lst.mergeSort compare_by_ones_then_value
  constructor
  · rfl
  · intro x
    constructor
    · rw [mergeSort_count]
    constructor
    · exact mergeSort_length lst compare_by_ones_then_value
    · intros i j hi hj
      have h := sort_property lst i j hi hj
      cases h with
      | inl h_lt => 
        left
        unfold count_ones at h_lt
        exact h_lt
      | inr h_eq_lt =>
        right
        constructor
        · unfold count_ones at h_eq_lt
          exact h_eq_lt.1
        · exact h_eq_lt.2