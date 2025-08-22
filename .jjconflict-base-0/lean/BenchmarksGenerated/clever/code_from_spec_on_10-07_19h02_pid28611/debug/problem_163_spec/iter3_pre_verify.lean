import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat → List Nat)
-- inputs
(a b : Nat) :=
let isAscendingBy2 (r : List Nat) :=
∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2
-- spec
let spec (result: List Nat) :=
result.all (fun n => n % 2 = 0) ∧ isAscendingBy2 result ∧
1 < result.length ∧
let min_a_b := min a b;
let max_a_b := max a b;
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
then result = []
else ((result[0]! = if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) ∧
(result[result.length-1]! = if 2 ∣ max_a_b then max_a_b else max_a_b - 1))
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def evenRange (start_even last_even : Nat) : List Nat :=
if start_even > last_even then []
else if start_even % 2 = 0 ∧ last_even % 2 = 0 then
  List.range ((last_even - start_even) / 2 + 1) |>.map (fun i => start_even + 2 * i)
else []

def implementation (a b: Nat) : List Nat := 
let min_a_b := min a b
let max_a_b := max a b
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1) then []
else
  let start_even := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
  let last_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
  evenRange start_even last_even

-- LLM HELPER
lemma dvd_iff_mod_eq_zero (a : Nat) : 2 ∣ a ↔ a % 2 = 0 := by
  constructor
  · intro h
    exact Nat.mod_eq_zero_of_dvd h
  · intro h
    exact Nat.dvd_of_mod_eq_zero h

-- LLM HELPER
lemma evenRange_all_even (start_even last_even : Nat) (h1 : start_even % 2 = 0) (h2 : last_even % 2 = 0) :
  (evenRange start_even last_even).all (fun n => n % 2 = 0) := by
  simp [evenRange]
  split_ifs with h3 h4
  · simp
  · simp [List.all_eq_true]
    intro x hx
    simp [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    simp [Nat.add_mod, h1]
  · simp

-- LLM HELPER
lemma evenRange_ascending (start_even last_even : Nat) (h1 : start_even % 2 = 0) (h2 : last_even % 2 = 0) :
  ∀ i, i < (evenRange start_even last_even).length - 1 → (evenRange start_even last_even)[i+1]?.getD 0 - (evenRange start_even last_even)[i]?.getD 0 = 2 := by
  simp [evenRange]
  split_ifs with h3 h4
  · simp
  · intro i hi
    simp [List.length_map, List.length_range] at hi
    have h_i : i < (last_even - start_even) / 2 + 1 := by omega
    have h_i_plus_1 : i + 1 < (last_even - start_even) / 2 + 1 := by omega
    simp [List.getElem?_map, List.getElem?_range, h_i, h_i_plus_1]
  · simp

-- LLM HELPER
lemma evenRange_first_last (start_even last_even : Nat) (h1 : start_even % 2 = 0) (h2 : last_even % 2 = 0) (h3 : start_even ≤ last_even) :
  let result := evenRange start_even last_even
  (result.length > 0 → result[0]! = start_even) ∧
  (result.length > 0 → result[result.length-1]! = last_even) := by
  simp [evenRange]
  split_ifs with h4 h5
  · simp at h4
    omega
  · simp [List.length_map, List.length_range]
    constructor
    · intro h_len
      simp [List.getElem_map, List.getElem_range]
    · intro h_len
      simp [List.getElem_map, List.getElem_range]
      have : (last_even - start_even) / 2 + 1 - 1 = (last_even - start_even) / 2 := by
        simp
      rw [this]
      have : start_even + 2 * ((last_even - start_even) / 2) = last_even := by
        have : last_even - start_even = 2 * ((last_even - start_even) / 2) := by
          rw [Nat.mul_comm]
          apply Nat.two_mul_div_two_of_even
          rw [Nat.even_sub h3]
          simp [Nat.even_iff_two_dvd, dvd_iff_mod_eq_zero, h1, h2]
        omega
      rw [this]
  · simp

-- LLM HELPER
lemma evenRange_length_gt_one (start_even last_even : Nat) (h1 : start_even % 2 = 0) (h2 : last_even % 2 = 0) (h3 : start_even + 2 ≤ last_even) :
  (evenRange start_even last_even).length > 1 := by
  simp [evenRange]
  split_ifs with h4 h5
  · simp at h4
    omega
  · simp [List.length_map, List.length_range]
    have : last_even - start_even ≥ 2 := by omega
    have : (last_even - start_even) / 2 ≥ 1 := by
      exact Nat.div_pos this (by norm_num)
    omega
  · simp

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  simp [problem_spec]
  use implementation a b
  constructor
  · rfl
  · simp [implementation]
    let min_a_b := min a b
    let max_a_b := max a b
    split_ifs with h
    · simp
      exact h.2
    · simp
      have h_not : ¬(min_a_b = max_a_b ∧ min_a_b % 2 = 1) := h
      push_neg at h_not
      let start_even := if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)
      let last_even := if 2 ∣ max_a_b then max_a_b else max_a_b - 1
      
      have h_start_even : start_even % 2 = 0 := by
        simp [start_even]
        split_ifs with h_div
        · rw [dvd_iff_mod_eq_zero] at h_div
          exact h_div
        · rw [dvd_iff_mod_eq_zero] at h_div
          simp at h_div
          rw [Nat.add_mod, h_div]
          simp
      
      have h_last_even : last_even % 2 = 0 := by
        simp [last_even]
        split_ifs with h_div
        · rw [dvd_iff_mod_eq_zero] at h_div
          exact h_div
        · rw [dvd_iff_mod_eq_zero] at h_div
          simp at h_div
          cases' Nat.mod_two_eq_zero_or_one max_a_b with h0 h1
          · contradiction
          · rw [h1, Nat.one_mod]
            cases' max_a_b with n
            · simp at h1
            · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      
      have h_le : start_even ≤ last_even := by
        simp [start_even, last_even]
        split_ifs with h1 h2
        · exact min_le_max
        · have : min_a_b + 1 ≤ max_a_b := by
            cases' h_not with h_neq h_even
            · exact Nat.succ_le_of_lt (lt_of_le_of_ne min_le_max h_neq)
            · have : min_a_b = max_a_b := le_antisymm min_le_max (by
                by_contra h_not_le
                exact h_neq (le_antisymm min_le_max (le_of_not_le h_not_le)))
              rw [dvd_iff_mod_eq_zero] at h2
              simp at h2
              rw [← this] at h2
              exact h_even h2
          have : max_a_b ≥ 1 := by omega
          omega
        · have : min_a_b ≤ max_a_b - 1 := by
            cases' h_not with h_neq h_even
            · have : min_a_b < max_a_b := lt_of_le_of_ne min_le_max h_neq
              omega
            · have : min_a_b = max_a_b := le_antisymm min_le_max (by
                by_contra h_not_le
                exact h_neq (le_antisymm min_le_max (le_of_not_le h_not_le)))
              rw [dvd_iff_mod_eq_zero] at h1
              simp at h1
              rw [this] at h1
              exact h_even h1
          exact this
        · have : min_a_b + 1 ≤ max_a_b - 1 := by
            cases' h_not with h_neq h_even
            · have : min_a_b + 2 ≤ max_a_b := by
                have : min_a_b < max_a_b := lt_of_le_of_ne min_le_max h_neq
                omega
              omega
            · have : min_a_b = max_a_b := le_antisymm min_le_max (by
                by_contra h_not_le
                exact h_neq (le_antisymm min_le_max (le_of_not_le h_not_le)))
              rw [dvd_iff_mod_eq_zero] at h1 h2
              simp at h1 h2
              rw [this] at h1
              exact h_even h1
          exact this
      
      constructor
      · exact evenRange_all_even start_even last_even h_start_even h_last_even
      constructor
      · exact evenRange_ascending start_even last_even h_start_even h_last_even
      constructor
      · cases' h_not with h_neq h_even
        · have : min_a_b < max_a_b := lt_of_le_of_ne min_le_max h_neq
          have : start_even + 2 ≤ last_even := by
            simp [start_even, last_even]
            split_ifs with h1 h2
            · omega
            · have : min_a_b + 1 + 2 ≤ max_a_b := by omega
              omega
            · have : min_a_b + 2 ≤ max_a_b - 1 := by
                have : min_a_b + 3 ≤ max_a_b := by omega
                omega
              omega
            · have : min_a_b + 1 + 2 ≤ max_a_b - 1 := by
                have : min_a_b + 4 ≤ max_a_b := by omega
                omega
              omega
          exact evenRange_length_gt_one start_even last_even h_start_even h_last_even this
        · have : min_a_b = max_a_b := le_antisymm min_le_max (by
            by_contra h_not_le
            exact h_neq (le_antisymm min_le_max (le_of_not_le h_not_le)))
          have : start_even = last_even := by
            simp [start_even, last_even, this]
            rw [dvd_iff_mod_eq_zero, dvd_iff_mod_eq_zero, h_even]
            simp
          have : evenRange start_even last_even = [start_even] := by
            simp [evenRange, this]
            split_ifs with h_gt
            · simp at h_gt
            · simp [h_start_even, h_last_even]
              simp [List.range_succ]
          rw [this]
          simp
      · have fl := evenRange_first_last start_even last_even h_start_even h_last_even h_le
        constructor
        · have : (evenRange start_even last_even).length > 0 := by
            cases' h_not with h_neq h_even
            · have : min_a_b < max_a_b := lt_of_le_of_ne min_le_max h_neq
              have : start_even + 2 ≤ last_even := by
                simp [start_even, last_even]
                split_ifs with h1 h2
                · omega
                · have : min_a_b + 1 + 2 ≤ max_a_b := by omega
                  omega
                · have : min_a_b + 2 ≤ max_a_b - 1 := by
                    have : min_a_b + 3 ≤ max_a_b := by omega
                    omega
                  omega
                · have : min_a_b + 1 + 2 ≤ max_a_b - 1 := by
                    have : min_a_b + 4 ≤ max_a_b := by omega
                    omega
                  omega
              have : (evenRange start_even last_even).length > 1 := evenRange_length_gt_one start_even last_even h_start_even h_last_even this
              omega
            · have : min_a_b = max_a_b := le_antisymm min_le_max (by
                by_contra h_not_le
                exact h_neq (le_antisymm min_le_max (le_of_not_le h_not_le)))
              have : start_even = last_even := by
                simp [start_even, last_even, this]
                rw [dvd_iff_mod_eq_zero, dvd_iff_mod_eq_zero, h_even]
                simp
              have : evenRange start_even last_even = [start_even] := by
                simp [evenRange, this]
                split_ifs with h_gt
                · simp at h_gt
                · simp [h_start_even, h_last_even]
                  simp [List.range_succ]
              rw [this]
              simp
          exact fl.1 this
        · have : (evenRange start_even last_even).length > 0 := by
            cases' h_not with h_neq h_even
            · have : min_a_b < max_a_b := lt_of_le_of_ne min_le_max h_neq
              have : start_even + 2 ≤ last_even := by
                simp [start_even, last_even]
                split_ifs with h1 h2
                · omega
                · have : min_a_b + 1 + 2 ≤ max_a_b := by omega
                  omega
                · have : min_a_b + 2 ≤ max_a_b - 1 := by
                    have : min_a_b + 3 ≤ max_a_b := by omega
                    omega
                  omega
                · have : min_a_b + 1 + 2 ≤ max_a_b - 1 := by
                    have : min_a_b + 4 ≤ max_a_b := by omega
                    omega
                  omega
              have : (evenRange start_even last_even).length > 1 := evenRange_length_gt_one start_even last_even h_start_even h_last_even this
              omega
            · have : min_a_b = max_a_b := le_antisymm min_le_max (by
                by_contra h_not_le
                exact h_neq (le_antisymm min_le_max (le_of_not_le h_not_le)))
              have : start_even = last_even := by
                simp [start_even, last_even, this]
                rw [dvd_iff_mod_eq_zero, dvd_iff_mod_eq_zero, h_even]
                simp
              have : evenRange start_even last_even = [start_even] := by
                simp [evenRange, this]
                split_ifs with h_gt
                · simp at h_gt
                · simp [h_start_even, h_last_even]
                  simp [List.range_succ]
              rw [this]
              simp
          exact fl.2 this