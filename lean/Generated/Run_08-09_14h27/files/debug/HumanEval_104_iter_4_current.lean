/- 
function_signature: "def unique_digits(x: List[nat]) -> List[nat]"
docstring: |
    Given a list of positive integers x. return a sorted list of all
    elements that hasn't any even digit.

    Note: Returned list should be sorted in increasing order.
test_cases:
  - input: [15, 33, 1422, 1]
    expected_output: [1, 15, 33]
  - input: [152, 323, 1422, 10]
    expected_output: []
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def has_even_digits (i: Nat): Bool :=
  (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0

-- LLM HELPER
def decidable_le : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

noncomputable def implementation (x: List Nat) : List Nat :=
  (List.filter (fun i => !(has_even_digits i)) x).toFinset.toList.mergeSort (fun x1 x2 => decide (x1 ≤ x2))

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(x: List Nat) :=
-- spec
let spec (result: List Nat) :=
  let has_even_digits(i: Nat): Bool :=
    (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0;
  (List.Sorted Nat.le result) ∧
  (forall i, i ∈ result ↔ (i ∈ x ∧ !(has_even_digits i)))
-- program termination
∃ result, implementation x = result ∧
spec result

-- LLM HELPER
lemma sorted_of_mergeSort (l : List Nat) : List.Sorted Nat.le (l.mergeSort (fun x1 x2 => decide (x1 ≤ x2))) := by
  rw [List.Sorted, List.Pairwise]
  rw [List.pairwise_iff_get]
  intros i j h
  have h_sorted := List.sorted_mergeSort
    (fun a b c => by simp [decide_eq_true_iff]; intros hab hbc; exact Nat.le_trans hab hbc)
    (fun a b => by simp [decide_eq_true_iff]; exact Nat.le_total a b)
    l
  rw [List.Sorted, List.Pairwise, List.pairwise_iff_get] at h_sorted
  have : decide (l.mergeSort (fun x1 x2 => decide (x1 ≤ x2))[i] ≤ l.mergeSort (fun x1 x2 => decide (x1 ≤ x2))[j]) = true := 
    h_sorted i j h
  rw [decide_eq_true_iff] at this
  exact this

-- LLM HELPER  
lemma mem_mergeSort_iff (l : List Nat) (x : Nat) :
  x ∈ l.mergeSort (fun x1 x2 => decide (x1 ≤ x2)) ↔ x ∈ l := by
  simp [List.mem_mergeSort]

theorem correctness
(x: List Nat)
: problem_spec implementation x
:= by
  unfold problem_spec
  use implementation x
  constructor
  · rfl
  constructor
  · -- Prove sortedness
    unfold implementation
    apply sorted_of_mergeSort
  · -- Prove membership equivalence
    intro i
    unfold implementation
    simp [mem_mergeSort_iff, List.mem_toFinset, has_even_digits]