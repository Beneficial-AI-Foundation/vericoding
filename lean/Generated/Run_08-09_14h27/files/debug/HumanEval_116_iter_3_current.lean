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
    Nat.digits 2 (result[i]!) < Nat.digits 2 (result[j]!) ∨
    (Nat.digits 2 (result[i]!) = Nat.digits 2 (result[j]!) ∧ result[i]! < result[j]!))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
lemma mergeSort_count (lst : List Nat) (cmp : Nat → Nat → Bool) (x : Nat) :
  (lst.mergeSort cmp).count x = lst.count x := by
  simp [List.mergeSort]

-- LLM HELPER
lemma mergeSort_length (lst : List Nat) (cmp : Nat → Nat → Bool) :
  (lst.mergeSort cmp).length = lst.length := by
  simp [List.mergeSort]

-- LLM HELPER
lemma mergeSort_sorted (lst : List Nat) :
  let result := lst.mergeSort compare_by_ones_then_value
  ∀ i j : Nat, i < j → j < result.length →
    count_ones (result[i]!) ≤ count_ones (result[j]!) ∧
    (count_ones (result[i]!) = count_ones (result[j]!) → result[i]! ≤ result[j]!) := by
  intro i j hi hj
  simp only [compare_by_ones_then_value, count_ones]
  sorry

-- LLM HELPER
lemma count_ones_eq_digits_count (n : Nat) :
  count_ones n = (Nat.digits 2 n).count 1 := by
  rfl

-- LLM HELPER
lemma sort_property (lst : List Nat) (i j : Nat) (hi : i < j) 
  (hj : j < (lst.mergeSort compare_by_ones_then_value).length) :
  count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) < count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) ∨
  (count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) = count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) ∧ 
   (lst.mergeSort compare_by_ones_then_value)[i]! < (lst.mergeSort compare_by_ones_then_value)[j]!) := by
  have h := mergeSort_sorted lst i j hi hj
  by_cases h_lt : count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) < count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!)
  · left
    exact h_lt
  · right
    have h_le := h.1
    have h_eq : count_ones ((lst.mergeSort compare_by_ones_then_value)[i]!) = count_ones ((lst.mergeSort compare_by_ones_then_value)[j]!) := by
      cases Nat.lt_or_eq_of_le h_le with
      | inl h_lt_contra => contradiction
      | inr h_eq => exact h_eq
    constructor
    · exact h_eq
    · have h_val := h.2 h_eq
      cases Nat.lt_or_eq_of_le h_val with
      | inl h_lt => exact h_lt
      | inr h_eq_val => 
        exfalso
        have : i = j := by
          sorry
        linarith [hi]

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
        rw [count_ones_eq_digits_count, count_ones_eq_digits_count] at h_lt
        simp [count_ones] at h_lt
        exact h_lt
      | inr h_eq_lt =>
        right
        constructor
        · rw [count_ones_eq_digits_count, count_ones_eq_digits_count] at h_eq_lt
          simp [count_ones] at h_eq_lt
          exact h_eq_lt.1
        · exact h_eq_lt.2