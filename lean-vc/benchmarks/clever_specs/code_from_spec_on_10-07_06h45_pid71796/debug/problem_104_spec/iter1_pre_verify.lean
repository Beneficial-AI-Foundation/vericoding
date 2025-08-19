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
def has_even_digits (i: Nat): Bool :=
  (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0

def implementation (x: List Nat) : List Nat := 
  (List.filter (fun i => !(has_even_digits i)) x).toFinset.toList.sort Nat.le

-- LLM HELPER
lemma filter_mem_iff (p : α → Prop) [DecidablePred p] (l : List α) (a : α) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a := by
  simp [List.mem_filter]

-- LLM HELPER
lemma toFinset_mem_iff (l : List α) [DecidableEq α] (a : α) :
  a ∈ l.toFinset ↔ a ∈ l := by
  simp [List.mem_toFinset]

-- LLM HELPER
lemma toList_mem_iff (s : Finset α) (a : α) :
  a ∈ s.toList ↔ a ∈ s := by
  simp [Finset.mem_toList]

-- LLM HELPER
lemma sort_sorted (l : List α) (r : α → α → Prop) [DecidableRel r] [IsTrans α r] :
  List.Sorted r (l.sort r) := by
  apply List.sorted_sort

-- LLM HELPER
lemma sort_mem_iff (l : List α) (r : α → α → Prop) [DecidableRel r] (a : α) :
  a ∈ l.sort r ↔ a ∈ l := by
  simp [List.mem_sort]

theorem correctness
(x: List Nat)
: problem_spec implementation x
:= by
  use implementation x
  constructor
  · rfl
  · constructor
    · -- Prove sorted
      apply sort_sorted
    · -- Prove membership equivalence
      intro i
      simp [implementation, has_even_digits]
      constructor
      · intro h
        rw [sort_mem_iff, toList_mem_iff, toFinset_mem_iff, filter_mem_iff] at h
        exact h
      · intro h
        rw [sort_mem_iff, toList_mem_iff, toFinset_mem_iff, filter_mem_iff]
        exact h