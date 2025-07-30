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
  List.mergeSort Nat.le (List.filter (fun i => !(has_even_digits i)) x)

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) (a : α) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a := by
  simp [List.mem_filter]

-- LLM HELPER
lemma mem_mergeSort_iff {α : Type*} (r : α → α → Prop) [DecidableRel r] (l : List α) (a : α) :
  a ∈ List.mergeSort r l ↔ a ∈ l := by
  simp [List.mem_mergeSort]

-- LLM HELPER
lemma mergeSort_sorted {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) :
  List.Sorted r (List.mergeSort r l) := by
  apply List.sorted_mergeSort

theorem correctness
(x: List Nat)
: problem_spec implementation x
:= by
  use List.mergeSort Nat.le (List.filter (fun i => !(has_even_digits i)) x)
  constructor
  · rfl
  · constructor
    · exact mergeSort_sorted Nat.le _
    · intro i
      constructor
      · intro h
        rw [mem_mergeSort_iff] at h
        rw [List.mem_filter] at h
        exact h
      · intro h
        rw [mem_mergeSort_iff]
        rw [List.mem_filter]
        exact h