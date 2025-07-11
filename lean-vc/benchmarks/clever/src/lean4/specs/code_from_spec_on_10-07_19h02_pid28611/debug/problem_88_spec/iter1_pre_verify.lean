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
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  lst.length > 0 →
  result.length = lst.length ∧
  (∀ i, i < result.length →
    result[i]! ∈ lst ∧
    lst[i]! ∈ result ∧
    result.count (lst[i]!) = lst.count (lst[i]!)) ∧
  (lst.head! + lst.getLast!) ≡ 1 [MOD 2] →
    result.Sorted Nat.le ∧
  (lst.head! + lst.getLast!) ≡ 0 [MOD 2] →
    result.Sorted (fun a b => a ≥ b)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def implementation (lst: List Nat) : List Nat := 
  if lst.length = 0 then []
  else if (lst.head! + lst.getLast!) % 2 = 1 then
    lst.mergeSort
  else
    lst.mergeSort.reverse

-- LLM HELPER
lemma list_mergeSort_length (lst: List Nat) : lst.mergeSort.length = lst.length := by
  simp [List.length_mergeSort]

-- LLM HELPER
lemma list_mergeSort_mem (lst: List Nat) (x: Nat) : x ∈ lst.mergeSort ↔ x ∈ lst := by
  simp [List.mem_mergeSort]

-- LLM HELPER
lemma list_mergeSort_count (lst: List Nat) (x: Nat) : lst.mergeSort.count x = lst.count x := by
  simp [List.count_mergeSort]

-- LLM HELPER
lemma list_mergeSort_sorted (lst: List Nat) : lst.mergeSort.Sorted Nat.le := by
  exact List.sorted_mergeSort lst

-- LLM HELPER
lemma list_reverse_length (lst: List Nat) : lst.reverse.length = lst.length := by
  simp [List.length_reverse]

-- LLM HELPER
lemma list_reverse_mem (lst: List Nat) (x: Nat) : x ∈ lst.reverse ↔ x ∈ lst := by
  simp [List.mem_reverse]

-- LLM HELPER
lemma list_reverse_count (lst: List Nat) (x: Nat) : lst.reverse.count x = lst.count x := by
  simp [List.count_reverse]

-- LLM HELPER
lemma list_reverse_sorted_ge (lst: List Nat) (h: lst.Sorted Nat.le) : lst.reverse.Sorted (fun a b => a ≥ b) := by
  rw [List.sorted_reverse]
  exact h

-- LLM HELPER
lemma nat_mod_two_eq_one_iff (n: Nat) : n % 2 = 1 ↔ n ≡ 1 [MOD 2] := by
  simp [ZMod.int_coe_eq_int_coe_iff]

-- LLM HELPER
lemma nat_mod_two_eq_zero_iff (n: Nat) : n % 2 = 0 ↔ n ≡ 0 [MOD 2] := by
  simp [ZMod.int_coe_eq_int_coe_iff]

-- LLM HELPER
lemma list_getElem_mem (lst: List Nat) (i: Nat) (h: i < lst.length) : lst[i]! ∈ lst := by
  simp [List.getElem_mem]

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  simp only [exists_prop]
  by_cases h_empty : lst.length = 0
  · simp [h_empty]
    intro h_pos
    exact Nat.lt_irrefl 0 h_pos
  · push_neg at h_empty
    have h_pos : lst.length > 0 := Nat.pos_of_ne_zero h_empty
    by_cases h_odd : (lst.head! + lst.getLast!) % 2 = 1
    · simp [if_neg (Ne.symm (ne_of_gt h_pos)), if_pos h_odd]
      constructor
      · exact h_pos
      constructor
      · exact list_mergeSort_length lst
      constructor
      · intro i hi
        constructor
        · rw [list_mergeSort_mem]
          exact list_getElem_mem lst i hi
        constructor
        · rw [← list_mergeSort_mem]
          exact list_getElem_mem lst.mergeSort i (by rwa [list_mergeSort_length])
        · rw [list_mergeSort_count]
      constructor
      · intro h_odd_mod
        exact list_mergeSort_sorted lst
      · intro h_even_mod
        rw [nat_mod_two_eq_one_iff] at h_odd
        rw [← nat_mod_two_eq_zero_iff] at h_even_mod
        have : (lst.head! + lst.getLast!) % 2 = 0 := by
          rw [← ZMod.int_coe_eq_int_coe_iff] at h_even_mod
          simp at h_even_mod
          exact h_even_mod
        rw [h_odd] at this
        norm_num at this
    · simp [if_neg (Ne.symm (ne_of_gt h_pos)), if_neg h_odd]
      constructor
      · exact h_pos
      constructor
      · rw [list_reverse_length, list_mergeSort_length]
      constructor
      · intro i hi
        constructor
        · rw [list_reverse_mem, list_mergeSort_mem]
          exact list_getElem_mem lst i (by rwa [← list_reverse_length, ← list_mergeSort_length])
        constructor
        · rw [← list_reverse_mem, ← list_mergeSort_mem]
          exact list_getElem_mem (lst.mergeSort.reverse) i hi
        · rw [list_reverse_count, list_mergeSort_count]
      constructor
      · intro h_odd_mod
        rw [nat_mod_two_eq_one_iff] at h_odd_mod
        push_neg at h_odd
        have : (lst.head! + lst.getLast!) % 2 ≠ 1 := by
          rw [← nat_mod_two_eq_one_iff]
          exact h_odd
        rw [← nat_mod_two_eq_one_iff] at this
        contradiction
      · intro h_even_mod
        exact list_reverse_sorted_ge lst.mergeSort (list_mergeSort_sorted lst)