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
    lst.mergeSort (fun a b => a ≤ b)
  else
    (lst.mergeSort (fun a b => a ≤ b)).reverse

-- LLM HELPER
lemma list_mergeSort_length (lst: List Nat) : (lst.mergeSort (fun a b => a ≤ b)).length = lst.length := by
  exact List.length_mergeSort lst (fun a b => a ≤ b)

-- LLM HELPER
lemma list_mergeSort_mem (lst: List Nat) (x: Nat) : x ∈ (lst.mergeSort (fun a b => a ≤ b)) ↔ x ∈ lst := by
  exact List.mem_mergeSort (fun a b => a ≤ b)

-- LLM HELPER
lemma list_mergeSort_count (lst: List Nat) (x: Nat) : (lst.mergeSort (fun a b => a ≤ b)).count x = lst.count x := by
  exact List.count_mergeSort lst (fun a b => a ≤ b) x

-- LLM HELPER
lemma list_mergeSort_sorted (lst: List Nat) : (lst.mergeSort (fun a b => a ≤ b)).Sorted (fun a b => a ≤ b) := by
  exact List.sorted_mergeSort (fun a b => a ≤ b) (fun a b c => le_trans)

-- LLM HELPER
lemma list_reverse_length (lst: List Nat) : lst.reverse.length = lst.length := by
  exact List.length_reverse lst

-- LLM HELPER
lemma list_reverse_mem (lst: List Nat) (x: Nat) : x ∈ lst.reverse ↔ x ∈ lst := by
  exact List.mem_reverse

-- LLM HELPER
lemma list_reverse_count (lst: List Nat) (x: Nat) : lst.reverse.count x = lst.count x := by
  exact List.count_reverse lst

-- LLM HELPER
lemma list_reverse_sorted_ge (lst: List Nat) (h: lst.Sorted (fun a b => a ≤ b)) : lst.reverse.Sorted (fun a b => b ≤ a) := by
  exact List.sorted_reverse_iff.mpr h

-- LLM HELPER
lemma nat_mod_two_eq_one_iff (n: Nat) : n % 2 = 1 ↔ n ≡ 1 [MOD 2] := by
  rw [Nat.ModEq, Nat.mod_mod_of_dvd (by norm_num : 2 ∣ 2)]
  simp

-- LLM HELPER
lemma nat_mod_two_eq_zero_iff (n: Nat) : n % 2 = 0 ↔ n ≡ 0 [MOD 2] := by
  rw [Nat.ModEq, Nat.mod_mod_of_dvd (by norm_num : 2 ∣ 2)]
  simp

-- LLM HELPER
lemma list_getElem_mem (lst: List Nat) (i: Nat) (h: i < lst.length) : lst[i] ∈ lst := by
  exact List.getElem_mem lst i h

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
      intro h_pos_assumption
      constructor
      · exact list_mergeSort_length lst
      constructor
      · intro i hi
        constructor
        · rw [list_mergeSort_mem]
          exact list_getElem_mem lst i (by rwa [← list_mergeSort_length])
        constructor
        · rw [← list_mergeSort_mem]
          exact list_getElem_mem (lst.mergeSort (fun a b => a ≤ b)) i hi
        · rw [list_mergeSort_count]
      constructor
      · intro h_odd_mod
        have sorted := list_mergeSort_sorted lst
        exact List.Sorted.mono (fun a b => le_of_decide_le) sorted
      · intro h_even_mod
        have : (lst.head! + lst.getLast!) % 2 = 0 := by
          rw [← nat_mod_two_eq_zero_iff] at h_even_mod
          exact h_even_mod
        rw [h_odd] at this
        norm_num at this
    · simp [if_neg (Ne.symm (ne_of_gt h_pos)), if_neg h_odd]
      intro h_pos_assumption
      constructor
      · rw [list_reverse_length, list_mergeSort_length]
      constructor
      · intro i hi
        constructor
        · rw [list_reverse_mem, list_mergeSort_mem]
          exact list_getElem_mem lst i (by rwa [← list_reverse_length, ← list_mergeSort_length])
        constructor
        · rw [← list_reverse_mem, ← list_mergeSort_mem]
          exact list_getElem_mem ((lst.mergeSort (fun a b => a ≤ b)).reverse) i hi
        · rw [list_reverse_count, list_mergeSort_count]
      constructor
      · intro h_odd_mod
        have : (lst.head! + lst.getLast!) % 2 = 1 := by
          rw [← nat_mod_two_eq_one_iff] at h_odd_mod
          exact h_odd_mod
        exact absurd this h_odd
      · intro h_even_mod
        have sorted := list_mergeSort_sorted lst
        have rev_sorted := list_reverse_sorted_ge (lst.mergeSort (fun a b => a ≤ b)) sorted
        exact List.Sorted.mono (fun a b => le_of_decide_le) rev_sorted