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
  exact List.count_mergeSort lst cmp x

-- LLM HELPER
lemma mergeSort_length (lst : List Nat) (cmp : Nat → Nat → Bool) :
  (lst.mergeSort cmp).length = lst.length := by
  exact List.length_mergeSort lst cmp

-- LLM HELPER
lemma compare_by_ones_transitive : 
  ∀ a b c, compare_by_ones_then_value a b = true → compare_by_ones_then_value b c = true → compare_by_ones_then_value a c = true := by
  intros a b c hab hbc
  unfold compare_by_ones_then_value at *
  simp at hab hbc
  by_cases h1 : count_ones a < count_ones b
  · simp [h1] at hab
    by_cases h2 : count_ones b < count_ones c
    · simp [h2] at hbc
      simp [Nat.lt_trans h1 h2]
    · simp [h2] at hbc
      by_cases h3 : count_ones b > count_ones c
      · contradiction
      · simp [Nat.not_lt] at h2 h3
        have : count_ones b = count_ones c := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h3) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h2))
        rw [this] at h1
        simp [h1]
  · simp [h1] at hab
    by_cases h4 : count_ones a > count_ones b
    · simp [h4] at hab
    · simp [h4] at hab
      have h_eq : count_ones a = count_ones b := by
        simp [Nat.not_lt] at h1 h4
        exact Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h4) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h1))
      by_cases h2 : count_ones b < count_ones c
      · simp [h2] at hbc
        rw [h_eq]
        simp [h2]
      · simp [h2] at hbc
        by_cases h3 : count_ones b > count_ones c
        · contradiction
        · simp [Nat.not_lt] at h2 h3
          have h_eq2 : count_ones b = count_ones c := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h3) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h2))
          rw [h_eq, h_eq2]
          simp [Nat.lt_trans hab hbc]

-- LLM HELPER
lemma sort_property (lst : List Nat) (i j : Nat) (hi : i < j) 
  (hj : j < (lst.mergeSort compare_by_ones_then_value).length) :
  count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) < count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) ∨
  (count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) = count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) ∧ 
   (lst.mergeSort compare_by_ones_then_value)[i]! < (lst.mergeSort compare_by_ones_then_value)[j]!) := by
  have sorted := List.sorted_mergeSort compare_by_ones_then_value lst
  have hi_bound : i < (lst.mergeSort compare_by_ones_then_value).length := Nat.lt_trans hi hj
  have h_relation := List.pairwise_of_sorted sorted i j hi_bound hj hi
  unfold compare_by_ones_then_value at h_relation
  by_cases h1 : count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) < count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!)
  · left; exact h1
  · right
    simp [Nat.not_lt] at h1
    by_cases h2 : count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) > count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!)
    · exfalso
      simp at h_relation
      cases' Nat.lt_or_eq_of_le h1 with h_lt h_eq
      · contradiction
      · exact h2 h_eq
    · simp [Nat.not_lt] at h1 h2
      have h_eq : count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) = count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) := 
        Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h2) (Nat.succ_le_of_lt (Nat.lt_of_not_ge h1))
      constructor
      · exact h_eq
      · simp at h_relation
        cases' Nat.lt_trichotomy (count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!)) (count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!)) with h_case h_other
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