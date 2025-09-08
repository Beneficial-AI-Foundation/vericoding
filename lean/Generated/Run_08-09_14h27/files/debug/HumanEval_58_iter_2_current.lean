import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def List.dedup_sorted (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs => 
    let rest := List.dedup_sorted xs
    match rest with
    | [] => [x]
    | y :: _ => if x = y then rest else x :: rest

noncomputable def implementation (l1 l2: List Int) : List Int :=
  let common := l1.filter (fun x => x ∈ l2)
  let sorted := common.toFinset.toList.mergeSort (· ≤ ·)
  sorted

def problem_spec
-- function signature
(implementation: List Int → List Int → List Int)
-- inputs
(l1 l2: List Int) :=
let is_unique (result: List Int) :=
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]! ≠ result[j]!;
let is_sorted (result: List Int) :=
  ∀ i, i < result.length - 1 →
  result[i]! ≤ result[i + 1]!;
-- spec
let spec (result: List Int) :=
  is_unique result ∧
  is_sorted result ∧
  (∀ i : Int, i ∈ result ↔ i ∈ l1 ∧ i ∈ l2)
-- program termination
∃ result, implementation l1 l2 = result ∧
spec result

-- LLM HELPER
lemma finset_toList_nodup (s : Finset Int) : s.toList.Nodup := by
  exact Finset.nodup_toList s

-- LLM HELPER  
lemma finset_toList_mem (s : Finset Int) (x : Int) : x ∈ s.toList ↔ x ∈ s := by
  exact Finset.mem_toList

-- LLM HELPER
lemma mergeSort_sorted (l : List Int) : (l.mergeSort (· ≤ ·)).Sorted (· ≤ ·) := by
  exact List.sorted_mergeSort (· ≤ ·) l

-- LLM HELPER
lemma mergeSort_perm (l : List Int) : l.mergeSort (· ≤ ·) ~ l := by
  exact List.perm_mergeSort (· ≤ ·) l

-- LLM HELPER
lemma sorted_implies_is_sorted (l : List Int) (h : l.Sorted (· ≤ ·)) :
  ∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]! := by
  intros i hi
  have h_pos : i < l.length := by omega
  have h_succ : i + 1 < l.length := by omega
  exact List.Sorted.rel_get_of_lt h (Nat.lt_succ_iff.mpr (Nat.le_refl i))

-- LLM HELPER
lemma nodup_implies_is_unique (l : List Int) (h : l.Nodup) :
  ∀ i j, i < l.length → j < l.length → i ≠ j → l[i]! ≠ l[j]! := by
  intros i j hi hj hne
  exact List.Nodup.get!_ne_get!_of_ne h hi hj hne

noncomputable theorem correctness
(l1 l2: List Int)
: problem_spec implementation l1 l2
:= by
  unfold problem_spec implementation
  let common := l1.filter (fun x => x ∈ l2)
  let result := common.toFinset.toList.mergeSort (· ≤ ·)
  use result
  constructor
  · rfl
  constructor
  · -- is_unique
    apply nodup_implies_is_unique
    have h1 : common.toFinset.toList.Nodup := finset_toList_nodup _
    exact h1.perm (mergeSort_perm _).symm
  constructor  
  · -- is_sorted
    apply sorted_implies_is_sorted
    exact mergeSort_sorted _
  · -- correct elements
    intro i
    constructor
    · -- i ∈ result → i ∈ l1 ∧ i ∈ l2
      intro hi
      have h1 : i ∈ common.toFinset.toList := by
        rw [← (mergeSort_perm _).mem_iff]
        exact hi
      have h2 : i ∈ common.toFinset := by
        rw [← finset_toList_mem]
        exact h1  
      have h3 : i ∈ common := Finset.mem_toFinset.mp h2
      rw [List.mem_filter] at h3
      exact ⟨h3.1, h3.2⟩
    · -- i ∈ l1 ∧ i ∈ l2 → i ∈ result  
      intro ⟨h1, h2⟩
      have h3 : i ∈ common := by
        rw [List.mem_filter]
        exact ⟨h1, h2⟩
      have h4 : i ∈ common.toFinset := Finset.mem_toFinset.mpr h3
      have h5 : i ∈ common.toFinset.toList := by
        rw [finset_toList_mem]
        exact h4
      rw [(mergeSort_perm _).mem_iff]
      exact h5

-- #test implementation [1, 4, 3, 34, 653, 2, 5] [5, 7, 1, 5, 9, 653, 121] = [1, 5, 653]
-- #test implementation [5, 3, 2, 8] [3, 2] = [2, 3]