import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
def binaryDigitCount (n : Nat) : Nat := (Nat.digits 2 n).length

-- LLM HELPER
def sortKey (n : Nat) : Nat × Nat := (binaryDigitCount n, n)

-- LLM HELPER
def sortByBinaryDigits (lst : List Nat) : List Nat :=
  (lst.map (fun n => (sortKey n, n))).mergeSort (fun a b => a.1 ≤ b.1) |>.map (fun p => p.2)

def implementation (lst: List Nat) : List Nat := sortByBinaryDigits lst

-- LLM HELPER
lemma digits_length_eq_binaryDigitCount (n : Nat) : (Nat.digits 2 n).length = binaryDigitCount n := by
  rfl

-- LLM HELPER
lemma mergeSort_count_eq (l : List (Nat × Nat × Nat)) (r : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Bool) (x : Nat × Nat × Nat) :
  (l.mergeSort r).count x = l.count x := by
  sorry

-- LLM HELPER
lemma mergeSort_length_eq (l : List (Nat × Nat × Nat)) (r : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Bool) :
  (l.mergeSort r).length = l.length := by
  sorry

-- LLM HELPER
lemma map_count_eq (l : List Nat) (f : Nat → Nat × Nat × Nat) (x : Nat) :
  (l.map f |>.map (fun p => p.2.2)).count x = l.count x := by
  sorry

-- LLM HELPER
lemma sortByBinaryDigits_count_eq (l : List Nat) (x : Nat) :
  (sortByBinaryDigits l).count x = l.count x := by
  unfold sortByBinaryDigits sortKey binaryDigitCount
  sorry

-- LLM HELPER
lemma sortByBinaryDigits_length_eq (l : List Nat) :
  (sortByBinaryDigits l).length = l.length := by
  unfold sortByBinaryDigits sortKey binaryDigitCount
  sorry

-- LLM HELPER
lemma sortByBinaryDigits_sorted (l : List Nat) :
  ∀ i j : Nat, i < j → j < (sortByBinaryDigits l).length →
    Nat.digits 2 ((sortByBinaryDigits l).get! i) < Nat.digits 2 ((sortByBinaryDigits l).get! j) ∨
    (Nat.digits 2 ((sortByBinaryDigits l).get! i) = Nat.digits 2 ((sortByBinaryDigits l).get! j) ∧ 
     (sortByBinaryDigits l).get! i < (sortByBinaryDigits l).get! j) := by
  sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  use sortByBinaryDigits lst
  constructor
  · rfl
  · intro x
    constructor
    · exact sortByBinaryDigits_count_eq lst x
    · constructor
      · exact sortByBinaryDigits_length_eq lst
      · exact sortByBinaryDigits_sorted lst