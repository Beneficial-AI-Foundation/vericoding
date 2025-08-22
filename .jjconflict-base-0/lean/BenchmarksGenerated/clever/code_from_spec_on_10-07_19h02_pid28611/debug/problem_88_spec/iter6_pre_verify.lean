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
  if lst = [] then []
  else if (lst.head! + lst.getLast?.getD 0) % 2 = 1 then
    lst.mergeSort (fun a b => decide (a ≤ b))
  else
    (lst.mergeSort (fun a b => decide (a ≤ b))).reverse

-- LLM HELPER
lemma le_decide_trans : ∀ a b c : Nat, decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true := by
  intro a b c hab hbc
  simp only [decide_eq_true_eq] at hab hbc ⊢
  exact le_trans hab hbc

-- LLM HELPER
lemma getLast_eq_getLast_getD (lst : List Nat) (h : lst ≠ []) : lst.getLast! = lst.getLast?.getD 0 := by
  cases lst with
  | nil => exact absurd rfl h
  | cons head tail => 
    simp [List.getLast!, List.getLast?]
    cases tail with
    | nil => simp
    | cons _ _ => simp [List.getLast!]

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  simp only [exists_prop]
  by_cases h_empty : lst = []
  · simp [h_empty]
    intro h_pos
    simp at h_pos
  · simp [if_neg h_empty]
    intro h_pos
    have h_nonempty : lst ≠ [] := h_empty
    have h_getLast : lst.getLast! = lst.getLast?.getD 0 := getLast_eq_getLast_getD lst h_nonempty
    rw [← h_getLast]
    by_cases h_odd : (lst.head! + lst.getLast!) % 2 = 1
    · simp [if_pos (by rw [h_getLast]; exact h_odd)]
      intro h_len h_perm h_odd_mod h_even_mod
      constructor
      · exact List.length_mergeSort lst
      constructor
      · intro i hi
        constructor
        · rw [List.mem_mergeSort]
          exact List.getElem_mem lst i (by rwa [← List.length_mergeSort])
        constructor
        · rw [← List.mem_mergeSort]
          exact List.getElem_mem (lst.mergeSort (fun a b => decide (a ≤ b))) i hi
        · rw [List.count_mergeSort]
      constructor
      · exact List.sorted_mergeSort (fun a b => decide (a ≤ b)) le_decide_trans
      · intro h_even_contradiction
        have : (lst.head! + lst.getLast!) % 2 = 0 := by
          rw [← ZMod.int_coe_eq_int_coe_iff] at h_even_contradiction
          simp at h_even_contradiction
          rw [← Nat.mod_two_eq_zero_iff_even] at h_even_contradiction
          exact h_even_contradiction
        rw [h_odd] at this
        norm_num at this
    · simp [if_neg (by rw [h_getLast]; exact h_odd)]
      intro h_len h_perm h_odd_mod h_even_mod
      constructor
      · rw [List.length_reverse, List.length_mergeSort]
      constructor
      · intro i hi
        constructor
        · rw [List.mem_reverse, List.mem_mergeSort]
          exact List.getElem_mem lst i (by rwa [← List.length_reverse, ← List.length_mergeSort])
        constructor
        · rw [← List.mem_reverse, ← List.mem_mergeSort]
          exact List.getElem_mem ((lst.mergeSort (fun a b => decide (a ≤ b))).reverse) i hi
        · rw [List.count_reverse, List.count_mergeSort]
      constructor
      · intro h_odd_contradiction
        have : (lst.head! + lst.getLast!) % 2 = 1 := by
          rw [← ZMod.int_coe_eq_int_coe_iff] at h_odd_contradiction
          simp at h_odd_contradiction
          rw [← Nat.mod_two_eq_one_iff_odd] at h_odd_contradiction
          exact h_odd_contradiction
        exact absurd this h_odd
      · have sorted := List.sorted_mergeSort (fun a b => decide (a ≤ b)) le_decide_trans
        exact List.sorted_reverse_iff.mpr sorted