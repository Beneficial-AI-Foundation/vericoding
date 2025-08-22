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

-- LLM HELPER
lemma mod_two_eq_zero_of_not_mod_two_eq_one (n : Nat) : ¬(n % 2 = 1) → n % 2 = 0 := by
  intro h
  have : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  interval_cases n % 2
  · rfl
  · contradiction

-- LLM HELPER
lemma zmod_two_eq_one_iff_mod_two_eq_one (n : Nat) : n ≡ 1 [MOD 2] ↔ n % 2 = 1 := by
  rw [ZMod.int_coe_eq_int_coe_iff]
  simp

-- LLM HELPER
lemma zmod_two_eq_zero_iff_mod_two_eq_zero (n : Nat) : n ≡ 0 [MOD 2] ↔ n % 2 = 0 := by
  rw [ZMod.int_coe_eq_int_coe_iff]
  simp

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
    by_cases h_odd : (lst.head! + lst.getLast!) % 2 = 1
    · simp [if_pos (by rw [h_getLast]; exact h_odd)]
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
      · intro h_mod
        exact List.sorted_mergeSort (fun a b => decide (a ≤ b)) le_decide_trans
      · intro h_even_mod
        have : (lst.head! + lst.getLast!) % 2 = 0 := by
          rw [← zmod_two_eq_zero_iff_mod_two_eq_zero] at h_even_mod
          exact h_even_mod
        rw [h_odd] at this
        norm_num at this
    · simp [if_neg (by rw [h_getLast]; exact h_odd)]
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
      · intro h_odd_mod
        have : (lst.head! + lst.getLast!) % 2 = 1 := by
          rw [← zmod_two_eq_one_iff_mod_two_eq_one] at h_odd_mod
          exact h_odd_mod
        exact absurd this h_odd
      · intro h_even_mod
        have sorted := List.sorted_mergeSort (fun a b => decide (a ≤ b)) le_decide_trans
        exact List.sorted_reverse_iff.mpr sorted