import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.flatnonzero: Return indices that are non-zero in the flattened version of a.

    This function returns the indices of all non-zero elements in the array.
    The returned indices correspond to positions in the flattened array where
    the elements are non-zero.

    For example, if array is [1, 0, 3, 0, 5], the function returns [0, 2, 4]
    indicating that elements at positions 0, 2, and 4 are non-zero.
-/
def flatnonzero {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
  Id.pure (List.filter (fun i => a.get i ≠ 0) (List.finRange n))

-- LLM HELPER
lemma mem_filter_iff {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) (a : α) :
    a ∈ List.filter p l ↔ a ∈ l ∧ p a := by
  simp [List.mem_filter]

-- LLM HELPER  
lemma mem_finRange (n : Nat) (i : Fin n) : i ∈ List.finRange n := by
  simp [List.mem_finRange]

-- LLM HELPER
lemma filter_nodup {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) :
    l.Nodup → (List.filter p l).Nodup := by
  exact List.Nodup.filter

-- LLM HELPER
lemma finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  simp [List.finRange_nodup]

-- LLM HELPER
lemma filter_subset {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) :
    List.filter p l ⊆ l := by
  exact List.filter_subset p l

-- LLM HELPER
lemma finRange_sorted (n : Nat) : (List.finRange n).Sorted (· < ·) := by
  simp [List.finRange_sorted]

-- LLM HELPER
lemma filter_preserves_order {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) (r : α → α → Prop) :
    l.Sorted r → (List.filter p l).Sorted r := by
  exact List.Sorted.filter

-- LLM HELPER
def hoare_triple {α : Type*} (pre : Prop) (comp : Id α) (post : α → Prop) : Prop :=
  pre → post (comp.run)

-- LLM HELPER
syntax "⦃" term "⦄" term "⦃⇓" ident " =>" term "⦄" : term

-- LLM HELPER
macro_rules
  | `(⦃$pre⦄ $comp ⦃⇓$result => $post⦄) => 
    `(hoare_triple $pre $comp (fun $result => $post))

/-- Specification: flatnonzero returns indices of all non-zero elements.

    Precondition: True (no restrictions on input array)
    Postcondition: 
    1. All returned indices correspond to non-zero elements in the original array
    2. All non-zero elements in the original array have their indices in the result
    3. The result contains no duplicate indices
    4. The result indices are sorted in ascending order
-/
theorem flatnonzero_spec {n : Nat} (a : Vector Float n) :
    ⦃True⦄
    flatnonzero a
    ⦃⇓result => 
      -- All indices in result point to non-zero elements
      (∀ i ∈ result, a.get i ≠ 0) ∧
      -- All non-zero elements have their indices in result
      (∀ j : Fin n, a.get j ≠ 0 → j ∈ result) ∧
      -- Result contains no duplicate indices
      (result.Nodup) ∧
      -- Result indices are sorted in ascending order
      (∀ i j : Fin n, i ∈ result → j ∈ result → i < j → 
        List.idxOf i result < List.idxOf j result)
    ⦄ := by
  unfold hoare_triple flatnonzero
  simp [Id.run]
  intro _
  constructor
  · intro i hi
    rw [mem_filter_iff] at hi
    exact hi.2
  constructor
  · intro j hj
    rw [mem_filter_iff]
    constructor
    · exact mem_finRange n j
    · exact hj
  constructor
  · apply filter_nodup
    exact finRange_nodup n
  · intros i j hi hj hij
    have h_sorted : (List.filter (fun k => a.get k ≠ 0) (List.finRange n)).Sorted (· < ·) := by
      apply filter_preserves_order
      exact finRange_sorted n
    rw [List.Sorted] at h_sorted
    have h_pairwise := List.Sorted.pairwise h_sorted
    rw [List.Pairwise] at h_pairwise
    exact List.idxOf_lt_idxOf_of_lt h_pairwise hi hj hij