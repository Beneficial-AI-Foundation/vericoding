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
def has_even_digits(i: Nat): Bool :=
  (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0

def implementation (x: List Nat) : List Nat := 
  (List.filter (fun i => !(has_even_digits i)) x).mergeSort (fun a b => a ≤ b)

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (p : α → Bool) (l : List α) (a : α) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a := by
  simp [List.mem_filter]

-- LLM HELPER
lemma mem_mergeSort_iff {α : Type*} (l : List α) (le : α → α → Bool) (a : α) :
  a ∈ List.mergeSort l le ↔ a ∈ l := by
  simp [List.mem_mergeSort]

-- LLM HELPER
lemma mergeSort_sorted (l : List Nat) :
  List.Sorted Nat.le (List.mergeSort l (fun a b => a ≤ b)) := by
  apply List.sorted_mergeSort

theorem correctness
(x: List Nat)
: problem_spec implementation x
:= by
  use (List.filter (fun i => !(has_even_digits i)) x).mergeSort (fun a b => a ≤ b)
  constructor
  · rfl
  · constructor
    · exact mergeSort_sorted _
    · intro i
      constructor
      · intro h
        rw [mem_mergeSort_iff] at h
        rw [mem_filter_iff] at h
        exact h
      · intro h
        rw [mem_mergeSort_iff]
        rw [mem_filter_iff]
        exact h