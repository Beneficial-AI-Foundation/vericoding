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
  (List.filter (fun i => !(has_even_digits i)) x).toSorted Nat.le

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) (a : α) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a := by
  simp [List.mem_filter]

-- LLM HELPER
lemma mem_toSorted_iff {α : Type*} [LinearOrder α] (l : List α) (a : α) :
  a ∈ l.toSorted (· ≤ ·) ↔ a ∈ l := by
  simp [List.mem_toSorted]

-- LLM HELPER
lemma toSorted_sorted {α : Type*} [LinearOrder α] (l : List α) :
  List.Sorted (· ≤ ·) (l.toSorted (· ≤ ·)) := by
  apply List.sorted_toSorted

theorem correctness
(x: List Nat)
: problem_spec implementation x
:= by
  use (List.filter (fun i => !(has_even_digits i)) x).toSorted Nat.le
  constructor
  · rfl
  · constructor
    · exact toSorted_sorted _
    · intro i
      constructor
      · intro h
        rw [mem_toSorted_iff] at h
        rw [List.mem_filter] at h
        exact h
      · intro h
        rw [mem_toSorted_iff]
        rw [List.mem_filter]
        exact h