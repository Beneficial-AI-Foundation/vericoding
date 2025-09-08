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
  exact List.sorted_mergeSort le_refl le_trans l

-- LLM HELPER
lemma sorted_implies_is_sorted (l : List Int) (h : l.Sorted (· ≤ ·)) :
  ∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]! := by
  intros i hi
  have h_succ : i + 1 < l.length := by omega
  cases' l with head tail
  · simp at hi
  · cases' i with i
    · simp [List.get!]
      by_cases h_empty : tail = []
      · simp [h_empty] at hi
      · have h_sorted : head ≤ tail[0]! := by
          have : List.Sorted (· ≤ ·) (head :: tail) := h
          rw [List.sorted_cons] at this
          cases' tail with t_head t_tail
          · contradiction
          · exact this.1
        simp [List.get!]
        exact h_sorted
    · have h_tail_sorted : List.Sorted (· ≤ ·) tail := by
        rw [List.sorted_cons] at h
        exact h.2
      simp [List.get!]
      by_cases h_i_bound : i < tail.length
      · by_cases h_succ_bound : i + 1 < tail.length
        · exact sorted_implies_is_sorted tail h_tail_sorted i (by simp; omega)
        · simp at h_succ
          omega
      · simp at hi
        omega

-- LLM HELPER
lemma nodup_implies_is_unique (l : List Int) (h : l.Nodup) :
  ∀ i j, i < l.length → j < l.length → i ≠ j → l[i]! ≠ l[j]! := by
  intros i j hi hj hne
  by_contra h_eq
  have h_get_i : i < l.length := hi
  have h_get_j : j < l.length := hj
  have : l.get ⟨i, h_get_i⟩ = l.get ⟨j, h_get_j⟩ := by
    simp [List.get!] at h_eq
    exact h_eq
  have : i = j := List.Nodup.get_inj_iff.mp ⟨h, this⟩
  exact hne this

theorem correctness
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
    exact List.Perm.nodup_iff.mpr ⟨List.perm_mergeSort _ _, h1⟩
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
        have perm := List.perm_mergeSort (· ≤ ·) common.toFinset.toList
        exact perm.symm.mem_iff.mpr hi
      have h2 : i ∈ common.toFinset := by
        rw [← finset_toList_mem]
        exact h1  
      have h3 : i ∈ common := by
        rw [← List.mem_toFinset]
        exact h2
      rw [List.mem_filter] at h3
      exact ⟨h3.1, h3.2⟩
    · -- i ∈ l1 ∧ i ∈ l2 → i ∈ result  
      intro ⟨h1, h2⟩
      have h3 : i ∈ common := by
        rw [List.mem_filter]
        exact ⟨h1, h2⟩
      have h4 : i ∈ common.toFinset := by
        rw [List.mem_toFinset]
        exact h3
      have h5 : i ∈ common.toFinset.toList := by
        rw [finset_toList_mem]
        exact h4
      have perm := List.perm_mergeSort (· ≤ ·) common.toFinset.toList
      exact perm.mem_iff.mpr h5

-- #test implementation [1, 4, 3, 34, 653, 2, 5] [5, 7, 1, 5, 9, 653, 121] = [1, 5, 653]
-- #test implementation [5, 3, 2, 8] [3, 2] = [2, 3]