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
  ∀ x ∈ evenRange start_even last_even, x % 2 = 0 := by
  simp [evenRange]
  split_ifs with h3 h4
  · simp
  · intro x hx
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
    ring
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
      have h_pos : (last_even - start_even) / 2 + 1 > 0 := by omega
      have h_last_idx : (last_even - start_even) / 2 < (last_even - start_even) / 2 + 1 := by omega
      simp [h_last_idx]
      have : start_even + 2 * ((last_even - start_even) / 2) = last_even := by
        have h_even_diff : (last_even - start_even) % 2 = 0 := by
          rw [Nat.sub_mod]
          simp [h1, h2]
        rw [← Nat.mul_div_cancel']
        · ring
        · exact Nat.dvd_of_mod_eq_zero h_even_diff
      exact this
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

-- LLM HELPER
lemma odd_sub_one_even (n : Nat) (h : n % 2 = 1) (h_pos : n > 0) : (n - 1) % 2 = 0 := by
  cases' Nat.mod_two_eq_zero_or_one n with h0 h1
  · rw [h0] at h
    simp at h
  · rw [h1] at h
    cases' n with m
    · simp at h_pos
    · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      simp [Nat.add_mod]
      rw [h1]
      simp

-- LLM HELPER
lemma evenRange_empty_when_start_gt_last (start_even last_even : Nat) (h : start_even > last_even) :
  evenRange start_even last_even = [] := by
  simp [evenRange, h]

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
    · -- Case: min_a_b = max_a_b ∧ min_a_b % 2 = 1, so result = []
      simp [List.all_eq_true]
      exact h.right
    · -- Case: ¬(min_a_b = max_a_b ∧ min_a_b % 2 = 1)
      push_neg at h
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
          · apply odd_sub_one_even
            · exact h1
            · by_contra h_zero
              simp at h_zero
              rw [h_zero] at h1
              simp at h1
      
      -- Check if start_even > last_even (empty case)
      by_cases h_order : start_even > last_even
      · -- Empty case - this should be impossible if we need length > 1
        have : evenRange start_even last_even = [] := evenRange_empty_when_start_gt_last _ _ h_order
        simp [List.all_eq_true, this]
        exfalso
        -- The problem spec requires length > 1, but we have empty list
        -- This means our inputs don't satisfy the precondition
        -- We need min_a_b ≠ max_a_b or min_a_b % 2 = 0
        cases' h with h_neq h_even
        · -- min_a_b ≠ max_a_b
          have : min_a_b < max_a_b := lt_of_le_of_ne min_le_max h_neq
          simp [start_even, last_even] at h_order
          split_ifs at h_order with h1 h2
          · omega
          · omega  
          · omega
          · omega
        · -- min_a_b % 2 = 0
          have : min_a_b = max_a_b := by
            by_contra h_neq
            have : min_a_b < max_a_b := lt_of_le_of_ne min_le_max h_neq
            simp [start_even, last_even] at h_order
            split_ifs at h_order with h1 h2
            · omega
            · omega
            · omega
            · omega
          have : min_a_b % 2 = 0 := h_even
          have : min_a_b = max_a_b ∧ min_a_b % 2 = 1 := by
            constructor
            · exact this
            · cases' Nat.mod_two_eq_zero_or_one min_a_b with h0 h1
              · rw [h0] at h_even
                simp at h_even
              · exact h1
          have : h this := by exact this
          simp at this
      
      · -- Non-empty case
        have h_le : start_even ≤ last_even := le_of_not_lt h_order
        
        simp [List.all_eq_true]
        constructor
        · exact evenRange_all_even start_even last_even h_start_even h_last_even
        constructor
        · exact evenRange_ascending start_even last_even h_start_even h_last_even
        
        -- Need to show length > 1
        have h_len : start_even + 2 ≤ last_even := by
          -- If not, then we would have start_even = last_even or start_even + 1 = last_even
          -- But this would mean min_a_b = max_a_b, which should trigger the empty case
          by_contra h_not_len
          simp at h_not_len
          have : start_even = last_even ∨ start_even + 1 = last_even := by omega
          cases' this with h_eq h_succ
          · -- start_even = last_even
            have : min_a_b = max_a_b := by
              simp [start_even, last_even] at h_eq
              split_ifs at h_eq with h1 h2
              · exact le_antisymm min_le_max (by omega)
              · omega
              · omega
              · omega
            cases' h with h_neq h_even
            · exact h_neq this
            · cases' Nat.mod_two_eq_zero_or_one min_a_b with h0 h1
              · exact h_even h0
              · have : this ∧ h1 := by exact ⟨this, h1⟩
                have : h this := by exact this
                simp at this
          · -- start_even + 1 = last_even
            simp [start_even, last_even] at h_succ
            split_ifs at h_succ with h1 h2
            · omega
            · omega
            · omega
            · omega
        
        constructor
        · exact evenRange_length_gt_one start_even last_even h_start_even h_last_even h_len
        · have fl := evenRange_first_last start_even last_even h_start_even h_last_even h_le
          have : (evenRange start_even last_even).length > 0 := by
            have : (evenRange start_even last_even).length > 1 := 
              evenRange_length_gt_one start_even last_even h_start_even h_last_even h_len
            omega
          constructor
          · exact fl.1 this
          · exact fl.2 this